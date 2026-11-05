import CondDatum

open Filter MeasureTheory Set Topology
open Fefferman Fefferman.ConcreteReal

noncomputable section

namespace CondFeffA

private theorem normSq3_nonneg' (v : RVector) : 0 ≤ normSq3 v := by
  unfold normSq3
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

private theorem normSq3_zero' {v : RVector} (h : normSq3 v = 0) : v = 0 := by
  unfold normSq3 at h
  obtain ⟨h01, h22⟩ := (add_eq_zero_iff_of_nonneg
    (add_nonneg (mul_self_nonneg (v 0)) (mul_self_nonneg (v 1)))
    (mul_self_nonneg (v 2))).mp h
  obtain ⟨h0, h1⟩ := mul_self_add_mul_self_eq_zero.mp h01
  have h2 : v 2 = 0 := mul_self_eq_zero.mp h22
  funext i
  change v i = 0
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

def differenceDensity (u v : RVelocity) (t : ℝ) (x : RSpace) : ℝ :=
  normSq3 (u x t - v x t)

def differenceEnergy (u v : RVelocity) (t : ℝ) : ℝ :=
  ∫ x, differenceDensity u v t x

private theorem density_continuous (u v : RVelocity) (t : ℝ)
    (hu : Continuous (fun x => u x t)) (hv : Continuous (fun x => v x t)) :
    Continuous (differenceDensity u v t) := by
  have h (i : Fin 3) : Continuous (fun x => (u x t - v x t) i) :=
    (continuous_apply i).comp (hu.sub hv)
  exact (((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))

private theorem density_integrable (u v : RVelocity) (t : ℝ)
    (hc : Continuous (differenceDensity u v t))
    (hu : squareIntegrableReal (fun x => u x t))
    (hv : squareIntegrableReal (fun x => v x t)) :
    Integrable (differenceDensity u v t) := by
  have hmaj : Integrable (fun x => 2 * (normSq3 (u x t) + normSq3 (v x t))) :=
    (Integrable.add hu hv).const_mul (2 : ℝ)
  apply hmaj.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖normSq3 (u x t - v x t)‖ ≤ 2 * (normSq3 (u x t) + normSq3 (v x t))
  rw [Real.norm_of_nonneg (normSq3_nonneg' _)]
  simp only [normSq3, Pi.sub_apply]
  nlinarith [sq_nonneg (u x t 0 + v x t 0), sq_nonneg (u x t 1 + v x t 1),
    sq_nonneg (u x t 2 + v x t 2)]

theorem velocity_eq_of_differenceEnergy_zero (u v : RVelocity) {t : ℝ}
    (hu : Continuous (fun x => u x t)) (hv : Continuous (fun x => v x t))
    (hLu : squareIntegrableReal (fun x => u x t))
    (hLv : squareIntegrableReal (fun x => v x t)) (hE : differenceEnergy u v t = 0) :
    ∀ x, u x t = v x t := by
  have hc := density_continuous u v t hu hv
  have hi := density_integrable u v t hc hLu hLv
  have hnn : 0 ≤ differenceDensity u v t := fun x => normSq3_nonneg' _
  have hae := (integral_eq_zero_iff_of_nonneg hnn hi).mp hE
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae hc
    (continuous_const : Continuous (0 : RSpace → ℝ))
  intro x
  exact sub_eq_zero.mp (normSq3_zero' (congrFun heq x))

/-- A.e. differential inequality for an absolutely continuous nonnegative
    energy. Only a finite bound for the coefficient on the comparison
    interval is needed. -/
theorem difference_gronwall {E : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T)
    (hac : AbsolutelyContinuousOnInterval E 0 T) (hi : E 0 = 0)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hd : ∀ᵐ t : ℝ, t ∈ Icc 0 T → deriv E t ≤ K * E t) :
    ∀ t ∈ Icc 0 T, E t = 0 := by
  intro t ht
  let g := fun x : ℝ => Real.exp (-K * x)
  have hg (x : ℝ) : 0 < g x := Real.exp_pos _
  have hdg (x : ℝ) : deriv g x = (-K) * g x := by
    have hlin : HasDerivAt (fun y : ℝ => -K * y) (-K) x := by
      simpa using (hasDerivAt_id x).const_mul (-K)
    simpa [g, mul_comm] using hlin.exp.deriv
  have hgc : ContDiff ℝ 1 g := by dsimp [g]; fun_prop
  have hga : AbsolutelyContinuousOnInterval g 0 t :=
    hgc.contDiffOn.absolutelyContinuousOnInterval
  have hea : AbsolutelyContinuousOnInterval E 0 t := by
    apply hac.mono
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  have hnon : (fun s => deriv g s * E s + g s * deriv E s)
      ≤ᵐ[volume.restrict (Ioc 0 t)] 0 := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hd] with x hx hxt
    have hb := hx ⟨hxt.1.le, hxt.2.trans ht.2⟩
    change deriv g x * E x + g x * deriv E x ≤ 0
    rw [hdg]
    nlinarith [mul_le_mul_of_nonneg_left hb (hg x).le]
  have hle : g t * E t - g 0 * E 0 ≤ 0 := by
    rw [← hga.integral_deriv_mul_eq_sub hea, intervalIntegral.integral_of_le ht.1]
    exact integral_nonpos_of_ae hnon
  rw [hi, mul_zero, sub_zero] at hle
  apply le_antisymm _ (hn t ht)
  by_contra! hpos
  exact (not_lt_of_ge hle) (mul_pos (hg t) hpos)

/-- The differential energy estimate is the PDE input. The time constant
    may depend on the particular local strong trajectory and interval. -/
def LocalDifferenceEstimate (u v : RVelocity) (T : ℝ) : Prop :=
  AbsolutelyContinuousOnInterval (differenceEnergy u v) 0 T ∧
    ∃ K : ℝ, ∀ᵐ t : ℝ, t ∈ Icc 0 T →
      deriv (differenceEnergy u v) t ≤ K * differenceEnergy u v t

/-- The energy identity and the bound for the trilinear difference term
    yield the precise scalar inequality used for uniqueness. -/
theorem localDifferenceEstimate_of_balance {u v : RVelocity} {T ν M : ℝ}
    (hν : 0 ≤ ν) (D B : ℝ → ℝ)
    (hac : AbsolutelyContinuousOnInterval (differenceEnergy u v) 0 T)
    (hbal : ∀ᵐ t : ℝ, t ∈ Icc 0 T →
      deriv (differenceEnergy u v) t / 2 + ν * D t = - B t)
    (hD : ∀ᵐ t : ℝ, t ∈ Icc 0 T → 0 ≤ D t)
    (hB : ∀ᵐ t : ℝ, t ∈ Icc 0 T → |B t| ≤ M * differenceEnergy u v t) :
    LocalDifferenceEstimate u v T := by
  refine ⟨hac, 2 * M, ?_⟩
  filter_upwards [hbal, hD, hB] with t hb hd hbound
  intro ht
  have hflux := (neg_le_abs (B t)).trans (hbound ht)
  nlinarith [hb ht, mul_nonneg hν (hd ht)]

theorem velocities_equal_on_interval {u v : RVelocity} {T : ℝ} (hT : 0 ≤ T)
    (hi : ∀ x, u x 0 = v x 0)
    (hs : ∀ t ∈ Icc 0 T, Continuous (fun x => u x t) ∧ Continuous (fun x => v x t))
    (hL : ∀ t ∈ Icc 0 T, squareIntegrableReal (fun x => u x t) ∧
      squareIntegrableReal (fun x => v x t))
    (hest : LocalDifferenceEstimate u v T) :
    ∀ t ∈ Icc 0 T, ∀ x, u x t = v x t := by
  have hi0 : differenceEnergy u v 0 = 0 := by
    simp [differenceEnergy, differenceDensity, hi, normSq3]
  obtain ⟨hac, K, hd⟩ := hest
  have hn (t : ℝ) (_ : t ∈ Icc 0 T) : 0 ≤ differenceEnergy u v t :=
    integral_nonneg (fun _ => normSq3_nonneg' _)
  have hz := difference_gronwall hT hac hi0 hn hd
  intro t ht
  exact velocity_eq_of_differenceEnergy_zero u v (hs t ht).1 (hs t ht).2
    (hL t ht).1 (hL t ht).2 (hz t ht)

theorem witness_local_trace_of_difference_estimate {c T : ℝ} (hT : 0 < T)
    {s : Solution realAnalysis} (v : RVelocity)
    (hw : globalSolution realAnalysis .wholeSpace unitViscosity (datum c) (zeroForce realAnalysis) s)
    (hi : ∀ x, v x 0 = datum c x)
    (hsv : ∀ t ∈ Icc 0 T, Continuous (fun x => v x t))
    (hLv : ∀ t ∈ Icc 0 T, squareIntegrableReal (fun x => v x t))
    (hest : LocalDifferenceEstimate s.velocity v T) :
    (fun t => s.velocity 0 t 0) =ᶠ[𝓝[Ici (0 : ℝ)] 0] (fun t => v 0 t 0) := by
  have hinitial : clause03 realAnalysis (datum c) s := hw.2.2.1
  have hu : vectorSmooth realAnalysis s.velocity := hw.2.2.2.1.1
  have h7 : clause07 realAnalysis s := hw.2.2.2.2
  obtain ⟨_, _, hb⟩ := h7
  have hsu (t : ℝ) (ht : t ∈ Icc 0 T) : Continuous (fun x => s.velocity x t) := by
    apply continuous_pi
    intro i
    have hc : ContinuousOn (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
        {z | 0 ≤ z.2} := (hu i).continuousOn
    exact hc.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ht.1)
  have he := velocities_equal_on_interval hT.le (fun x => (hinitial x).trans (hi x).symm)
    (fun t ht => ⟨hsu t ht, hsv t ht⟩) (fun t ht => ⟨(hb t ht.1).1, hLv t ht⟩) hest
  filter_upwards [Icc_mem_nhdsGE hT] with t ht
  exact congrFun (he t ht 0) 0

end CondFeffA
end

#print axioms CondFeffA.difference_gronwall
#print axioms CondFeffA.localDifferenceEstimate_of_balance
#print axioms CondFeffA.velocity_eq_of_differenceEnergy_zero
#print axioms CondFeffA.velocities_equal_on_interval
#print axioms CondFeffA.witness_local_trace_of_difference_estimate
