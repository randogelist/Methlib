import SingularClosure.CriticalLimitUniform
import SingularClosure.SobolevTimeL2Compactness

/-! Strong L2-in-time H1 compactness from the critical estimates. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter Metric
open scoped BigOperators Topology Interval ENNReal

namespace SingularClosure

noncomputable section

/-- A fixed finite Fourier cutoff maps H0 continuously into any integral order. -/
def criticalTorusFiniteLift (s K : ℕ) : TorusSobolev 0 →L[ℂ] TorusSobolev s :=
  ∑ ki ∈ sobolevCutoffIndices K,
    ((((torusSobolevRepr s).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (lp.singleContinuousLinearMap ℂ (fun _ : FourierIndex => ℂ) 2 ki)).comp
      (((torusSobolevWeight ki.1 : ℂ) ^ s) • ContinuousLinearMap.id ℂ ℂ)).comp
      (torusSobolevH0Coeff ki.1 ki.2)

theorem criticalTorusFiniteLift_eq_cutoff (s K : ℕ)
    (v : TorusSobolev 0) (u : TorusSobolev s) (hcoeff : v.val = u.val) :
    criticalTorusFiniteLift s K v = torusSobolevCutoff s K u := by
  rw [torusSobolevCutoff_eq_sum_rankOne]
  simp only [criticalTorusFiniteLift, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro ki hki
  change (torusSobolevRepr s).symm (lp.single 2 ki
      ((torusSobolevWeight ki.1 : ℂ) ^ s * torusSobolevH0Coeff ki.1 ki.2 v)) =
    (torusSobolevRepr s).symm (lp.single 2 ki
      ((torusSobolevWeight ki.1 : ℂ) ^ s * u.val ki.1 ki.2))
  rw [torusSobolevH0Coeff_apply, hcoeff]

theorem GalerkinSolution.criticalToTorusH1_state
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) : criticalToTorusH1 (g.criticalState 3 t) = g.sobolevState 1 t := by
  apply Subtype.ext
  rw [criticalToTorusH1_coeff, g.criticalState_coeff 3 ht, g.sobolevState_coeff 1 ht]

theorem GalerkinSolution.critical_H1_time_tail
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (T B : ℝ) (hT : 0 ≤ T)
    (hbudget : (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ B)
    (K : ℕ) (hK : 0 < K) :
    (∫ t in (0 : ℝ)..T,
      ‖g.sobolevState 1 t - torusSobolevCutoff 1 K (g.sobolevState 1 t)‖ ^ 2) ≤
      4 * (K : ℝ)⁻¹ * B := by
  have h := criticalToTorusH1_time_tail_sq (g.criticalState 3) T B hT
    ((g.criticalState_continuousOn 3).mono (fun t ht => ht.1)) hbudget K hK
  have heq : (∫ t in (0 : ℝ)..T,
      ‖criticalToTorusH1 (g.criticalState 3 t) -
        torusSobolevCutoff 1 K (criticalToTorusH1 (g.criticalState 3 t))‖ ^ 2) =
      ∫ t in (0 : ℝ)..T,
        ‖g.sobolevState 1 t - torusSobolevCutoff 1 K (g.sobolevState 1 t)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := by simpa only [uIcc_of_le hT] using ht
    rw [g.criticalToTorusH1_state t ht'.1]
  rw [heq] at h
  exact h

private theorem critical_norm_sub_three_parts
    {E : Type*} [NormedAddCommGroup E] (u v p q : E) :
    ‖u - v‖ ^ 2 ≤ 3 * ‖u - p‖ ^ 2 + 3 * ‖p - q‖ ^ 2 + 3 * ‖v - q‖ ^ 2 := by
  have heq : u - v = (u - p) + (p - q) + (q - v) := by abel
  have hnorm : ‖u - v‖ ≤ ‖u - p‖ + ‖p - q‖ + ‖v - q‖ := by
    rw [heq]
    calc
      _ ≤ ‖(u - p) + (p - q)‖ + ‖q - v‖ := norm_add_le _ _
      _ ≤ (‖u - p‖ + ‖p - q‖) + ‖q - v‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by rw [norm_sub_rev q v]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg (‖u - p‖ - ‖p - q‖), sq_nonneg (‖u - p‖ - ‖v - q‖),
    sq_nonneg (‖p - q‖ - ‖v - q‖)]

/-- The high-frequency energy budget and the finite-band gap control the full time-H1 gap. -/
theorem criticalGalerkin_H1_time_difference_bound
    {ν : ℝ} {a b : Field} {N M : ℕ}
    (g : GalerkinSolution ν a N) (h : GalerkinSolution ν b M)
    (T B η : ℝ) (hT : 0 ≤ T) (hη : 0 ≤ η)
    (hg : (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ B)
    (hh : (∫ t in (0 : ℝ)..T, ‖h.criticalState 3 t‖ ^ 2) ≤ B)
    (K : ℕ) (hK : 0 < K)
    (hgap : ∀ t ∈ Icc (0 : ℝ) T,
      ‖torusSobolevCutoff 1 K (g.sobolevState 1 t) -
        torusSobolevCutoff 1 K (h.sobolevState 1 t)‖ ≤ η) :
    (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t - h.sobolevState 1 t‖ ^ 2) ≤
      24 * (K : ℝ)⁻¹ * B + 3 * T * η ^ 2 := by
  have hgcont : ContinuousOn (g.sobolevState 1) (Icc (0 : ℝ) T) :=
    (g.sobolevState_continuousOn 1).mono (fun t ht => ht.1)
  have hhcont : ContinuousOn (h.sobolevState 1) (Icc (0 : ℝ) T) :=
    (h.sobolevState_continuousOn 1).mono (fun t ht => ht.1)
  have hgp := (torusSobolevCutoff 1 K).continuous.comp_continuousOn hgcont
  have hhp := (torusSobolevCutoff 1 K).continuous.comp_continuousOn hhcont
  have hgi := ((hgcont.sub hgp).norm.pow 2).intervalIntegrable_of_Icc hT
  have hhi := ((hhcont.sub hhp).norm.pow 2).intervalIntegrable_of_Icc hT
  have hbound : (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t - h.sobolevState 1 t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T,
        3 * ‖g.sobolevState 1 t - torusSobolevCutoff 1 K (g.sobolevState 1 t)‖ ^ 2 +
        3 * η ^ 2 +
        3 * ‖h.sobolevState 1 t - torusSobolevCutoff 1 K (h.sobolevState 1 t)‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on hT
      (((hgcont.sub hhcont).norm.pow 2).intervalIntegrable_of_Icc hT)
      (((hgi.const_mul 3).add intervalIntegrable_const).add (hhi.const_mul 3))
    intro t ht
    change ‖g.sobolevState 1 t - h.sobolevState 1 t‖ ^ 2 ≤
      3 * ‖g.sobolevState 1 t - torusSobolevCutoff 1 K (g.sobolevState 1 t)‖ ^ 2 +
      3 * η ^ 2 +
      3 * ‖h.sobolevState 1 t - torusSobolevCutoff 1 K (h.sobolevState 1 t)‖ ^ 2
    have hthree := critical_norm_sub_three_parts (g.sobolevState 1 t) (h.sobolevState 1 t)
      (torusSobolevCutoff 1 K (g.sobolevState 1 t))
      (torusSobolevCutoff 1 K (h.sobolevState 1 t))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hgap t ht) 2
    nlinarith
  rw [intervalIntegral.integral_add ((hgi.const_mul 3).add intervalIntegrable_const)
      (hhi.const_mul 3),
    intervalIntegral.integral_add (hgi.const_mul 3) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hbound
  have hgtail := g.critical_H1_time_tail T B hT hg K hK
  have hhtail := h.critical_H1_time_tail T B hT hh K hK
  change (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t - h.sobolevState 1 t‖ ^ 2) ≤
    3 * _ + T * (3 * η ^ 2) + 3 * _ at hbound
  nlinarith

def GalerkinSolution.criticalTimeH1L2 {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (T : ℝ) : TimeH1L2 T :=
  (g.sobolevState_memLp 1 T 2).toLp (g.sobolevState 1)

theorem criticalTimeH1L2_sub_norm_sq
    {ν : ℝ} {a b : Field} {N M : ℕ}
    (g : GalerkinSolution ν a N) (h : GalerkinSolution ν b M)
    (T : ℝ) (hT : 0 ≤ T) :
    ‖g.criticalTimeH1L2 T - h.criticalTimeH1L2 T‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t - h.sobolevState 1 t‖ ^ 2 := by
  rw [timeH1L2_norm_sq]
  calc
    _ = ∫ t in Icc (0 : ℝ) T, ‖g.sobolevState 1 t - h.sobolevState 1 t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (g.criticalTimeH1L2 T) (h.criticalTimeH1L2 T),
        (g.sobolevState_memLp 1 T 2).coeFn_toLp,
        (h.sobolevState_memLp 1 T 2).coeFn_toLp] with t hsub hg hh
      rw [hsub]
      change ‖(g.sobolevState_memLp 1 T 2).toLp (g.sobolevState 1) t -
        (h.sobolevState_memLp 1 T 2).toLp (h.sobolevState 1) t‖ ^ 2 = _
      rw [hg, hh]
    _ = _ := by
      rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

/-- Uniform H0 convergence and an H^(3/2) time budget imply a genuine L2 H1 limit. -/
theorem CRITICAL_GALERKIN_L2H1_LIMIT_OF_H0_UNIFORM
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (u0 : Icc (0 : ℝ) T → TorusSobolev 0)
    (hconv : TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
      (g n).sobolevState 0 t.val) u0 atTop)
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B) :
    ∃ u1 : TimeH1L2 T,
      Tendsto (fun n => (g n).criticalTimeH1L2 T) atTop (𝓝 u1) := by
  have hcauchy : CauchySeq (fun n => (g n).criticalTimeH1L2 T) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (48 * B / ε ^ 2)
    let J := K + 1
    have hJ : 0 < J := Nat.succ_pos K
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
    have hlarge : 48 * B < (J : ℝ) * ε ^ 2 := by
      have hKJ : (K : ℝ) < J := by dsimp [J]; norm_cast; omega
      exact (div_lt_iff₀ (sq_pos_of_pos hε)).mp (hK.trans hKJ)
    have htail : 24 * (J : ℝ)⁻¹ * B < ε ^ 2 / 2 := by
      have hdiv : 24 * B / (J : ℝ) < ε ^ 2 / 2 :=
        (div_lt_iff₀ hJr).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    let η := Real.sqrt (ε ^ 2 / (12 * (T + 1)))
    have hη : 0 < η := Real.sqrt_pos.mpr (by positivity)
    have hηsq : η ^ 2 = ε ^ 2 / (12 * (T + 1)) := Real.sq_sqrt (by positivity)
    have hheadsmall : 3 * T * η ^ 2 < ε ^ 2 / 2 := by
      rw [hηsq]
      have hden : 0 < 12 * (T + 1) := by positivity
      have heq : (ε ^ 2 / (12 * (T + 1))) * (12 * (T + 1)) = ε ^ 2 :=
        div_mul_cancel₀ _ hden.ne'
      have hnonneg : 0 ≤ ε ^ 2 / (12 * (T + 1)) := by positivity
      nlinarith [sq_pos_of_pos hε]
    have hlift := (criticalTorusFiniteLift 1 J).uniformContinuous.comp_tendstoUniformly hconv
    obtain ⟨L, hL⟩ := eventually_atTop.mp
      (Metric.tendstoUniformly_iff.mp hlift (η / 2) (half_pos hη))
    refine ⟨L, ?_⟩
    intro m hm n hn
    have hgap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        ‖torusSobolevCutoff 1 J ((g m).sobolevState 1 t) -
          torusSobolevCutoff 1 J ((g n).sobolevState 1 t)‖ ≤ η := by
      have hident (j : ℕ) : criticalTorusFiniteLift 1 J ((g j).sobolevState 0 t) =
          torusSobolevCutoff 1 J ((g j).sobolevState 1 t) := by
        apply criticalTorusFiniteLift_eq_cutoff
        rw [(g j).sobolevState_coeff 0 ht.1, (g j).sobolevState_coeff 1 ht.1]
      have hm' := hL m hm ⟨t, ht⟩
      have hn' := hL n hn ⟨t, ht⟩
      change dist (criticalTorusFiniteLift 1 J (u0 ⟨t, ht⟩))
        (criticalTorusFiniteLift 1 J ((g m).sobolevState 0 t)) < η / 2 at hm'
      change dist (criticalTorusFiniteLift 1 J (u0 ⟨t, ht⟩))
        (criticalTorusFiniteLift 1 J ((g n).sobolevState 0 t)) < η / 2 at hn'
      rw [hident m] at hm'
      rw [hident n] at hn'
      rw [← dist_eq_norm]
      have htri := dist_triangle_left
        (torusSobolevCutoff 1 J ((g m).sobolevState 1 t))
        (torusSobolevCutoff 1 J ((g n).sobolevState 1 t))
        (criticalTorusFiniteLift 1 J (u0 ⟨t, ht⟩))
      linarith
    have hnumeric := criticalGalerkin_H1_time_difference_bound (g m) (g n)
      T B η hT hη.le (hbudget m) (hbudget n) J hJ hgap
    rw [← criticalTimeH1L2_sub_norm_sq (g m) (g n) T hT] at hnumeric
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
      (hnumeric.trans_lt (by linarith))
  exact cauchySeq_tendsto_of_complete hcauchy

/-- Simultaneous strong H0-uniform and L2 H1 limits from the three critical estimates. -/
theorem CRITICAL_GALERKIN_H0_L2H1_SUBSEQUENCE
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (T A B D : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hstate : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(g n).criticalState 1 t‖ ≤ A)
    (hspace : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B)
    (htime : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ u : Icc (0 : ℝ) T → CriticalSobolev 1, ∃ u1 : TimeH1L2 T, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ t, ‖u t‖ ≤ A) ∧
      Continuous (fun t => criticalToTorusH0 1 (by norm_num) (u t)) ∧
      TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
        (g (φ n)).sobolevState 0 t.val)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop ∧
      Tendsto (fun n => (g (φ n)).criticalTimeH1L2 T) atTop (𝓝 u1) := by
  obtain ⟨u, φ, hφ, hu, hcont, hconv⟩ :=
    CRITICAL_GALERKIN_H0_UNIFORM_SUBSEQUENCE ν a N g T A D hA hD hstate htime
  obtain ⟨u1, h1⟩ := CRITICAL_GALERKIN_L2H1_LIMIT_OF_H0_UNIFORM ν (fun n => a (φ n))
    (fun n => N (φ n)) (fun n => g (φ n)) T B hT hB
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) hconv (fun n => hspace (φ n))
  exact ⟨u, u1, φ, hφ, hu, hcont, hconv, h1⟩

end

end SingularClosure
