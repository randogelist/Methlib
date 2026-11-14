import SingularClosure.CriticalPositiveTimeEnergy
import SingularClosure.HighOrderEstimate
import SingularClosure.CriticalPositiveTimeSeed

/-! Positive-time Galerkin smoothing from an actual integrated H2 seed.
No initial higher Sobolev bound occurs in the conclusion or in the seed.
Each order uses a bounded-energy time in an earlier interval and the
proved finite-dimensional high-order evolution inequality. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped Interval

namespace SingularClosure
noncomputable section

theorem critical_positive_time_order_from_integrals
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (m : ℕ)
    (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (Y S : ℝ) (hY : 0 ≤ Y) (hS : 0 ≤ S)
    (hybudget : ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
      (∫ s in (τ / 2)..T, highOrderEnergy m N (g.coeff s)) ≤ Y)
    (h2budget : ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
      (∫ s in (τ / 2)..T, highOrderEnergy 2 N (g.coeff s)) ≤ S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B := by
  obtain ⟨C, hC, hineq⟩ := GALERKIN_HIGH_ORDER_DIFFERENTIAL_INEQUALITY m
  let M : ℝ := 2 * ν * T + C / ν * S
  let Y₀ : ℝ := Y / (τ - τ / 2)
  have hhalf : 0 < τ / 2 := by positivity
  have hgap : 0 < τ - τ / 2 := by linarith
  refine ⟨Y₀ * Real.exp M, mul_nonneg (div_nonneg hY hgap.le) (Real.exp_pos _).le, ?_⟩
  intro N g
  have hcont (q : ℕ) : ContinuousOn (fun s => highOrderEnergy q N (g.coeff s))
      (Icc (τ / 2) T) :=
    (g.highOrderEnergy_continuousOn q).mono (fun s hs => hhalf.le.trans hs.1)
  have hi (q : ℕ) : IntervalIntegrable (fun s => highOrderEnergy q N (g.coeff s))
      volume (τ / 2) T :=
    (hcont q).intervalIntegrable_of_Icc (by linarith)
  have havg : (∫ s in (τ / 2)..τ, highOrderEnergy m N (g.coeff s)) ≤ Y := by
    apply le_trans _ (hybudget N g)
    exact intervalIntegral.integral_mono_interval le_rfl (by linarith) hτT.le
      (Filter.Eventually.of_forall (fun s => highOrderEnergy_nonneg m N (g.coeff s))) (hi m)
  obtain ⟨r, hr, hrY⟩ := critical_exists_energy_le_average
    (show τ / 2 < τ by linarith)
    ((hcont m).mono (Icc_subset_Icc le_rfl hτT.le)) havg
  have hr0 : 0 < r := hhalf.trans_le hr.1
  have hrT : r ≤ T := hr.2.trans hτT.le
  let y : ℝ → ℝ := fun t => highOrderEnergy m N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (highOrderEnergy (m + 1) N (g.coeff t))
  let d : ℝ → ℝ := fun t => (-2 * ν) *
    (highOrderEnergy (m + 1) N (g.coeff t) - highOrderEnergy m N (g.coeff t)) -
      2 * highOrderNonlinearPower m N (g.coeff t)
  let A : ℝ → ℝ := fun t => 2 * ν + C / ν * highOrderEnergy 2 N (g.coeff t)
  have hcontR (q : ℕ) : ContinuousOn (fun s => highOrderEnergy q N (g.coeff s))
      (Icc r T) := (hcont q).mono (Icc_subset_Icc hr.1 le_rfl)
  have hy : ContinuousOn y (Icc r T) := hcontR m
  have hz : ContinuousOn z (Icc r T) :=
    Real.continuous_sqrt.comp_continuousOn (hcontR (m + 1))
  have hA : ContinuousOn A (Icc r T) :=
    continuousOn_const.add (continuousOn_const.mul (hcontR 2))
  have hA_nonneg (t : ℝ) (_ht : t ∈ Icc r T) : 0 ≤ A t :=
    add_nonneg (mul_nonneg (by norm_num) hν.le)
      (mul_nonneg (div_nonneg hC.le hν.le) (highOrderEnergy_nonneg 2 N (g.coeff t)))
  have hd (t : ℝ) (ht : t ∈ Ioo r T) : HasDerivAt y (d t) t :=
    (g.highOrderEnergy_balance m (hr0.le.trans ht.1.le)).hasDerivAt
      (Ici_mem_nhds (hr0.trans ht.1))
  have hl (t : ℝ) (ht : t ∈ Ioo r T) : d t + ν * z t ^ 2 ≤ A t * y t := by
    obtain ⟨d', hd', hb⟩ := hineq ν hν (a N) N g t (hr0.le.trans ht.1.le)
    have heq : d t = d' := (hd t ht).unique
      (hd'.hasDerivAt (Ici_mem_nhds (hr0.trans ht.1)))
    dsimp only [z]
    rw [Real.sq_sqrt (highOrderEnergy_nonneg _ _ _), heq]
    exact hb
  have h2R : (∫ s in r..T, highOrderEnergy 2 N (g.coeff s)) ≤ S := by
    apply le_trans _ (h2budget N g)
    exact intervalIntegral.integral_mono_interval hr.1 hrT le_rfl
      (Filter.Eventually.of_forall (fun s => highOrderEnergy_nonneg 2 N (g.coeff s))) (hi 2)
  have hAR : (∫ s in r..T, A s) ≤ M := by
    have hiR : IntervalIntegrable (fun s => highOrderEnergy 2 N (g.coeff s)) volume r T :=
      (hcontR 2).intervalIntegrable_of_Icc hrT
    dsimp only [A, M]
    rw [intervalIntegral.integral_add intervalIntegrable_const (hiR.const_mul (C / ν)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2R (div_nonneg hC.le hν.le),
      mul_nonneg hν.le hr0.le]
  have hb := critical_shifted_linear_energy_budget hν.le hrT hy hz hA
    (fun t _ => highOrderEnergy_nonneg m N (g.coeff t)) hA_nonneg hrY hd hl hAR
  intro t ht
  have hrt : r ≤ t := hr.2.trans ht.1
  have hmon : (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤
      ∫ s in r..t, highOrderEnergy (m + 1) N (g.coeff s) := by
    exact intervalIntegral.integral_mono_interval hr.2 ht.1 le_rfl
      (Filter.Eventually.of_forall (fun s => highOrderEnergy_nonneg (m + 1) N (g.coeff s)))
      (((hcontR (m + 1)).mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc hrt)
  have hzsq (s : ℝ) : z s ^ 2 = highOrderEnergy (m + 1) N (g.coeff s) :=
    Real.sq_sqrt (highOrderEnergy_nonneg _ _ _)
  have hvalue := hb t ⟨hrt, ht.2⟩
  simp only [hzsq] at hvalue
  exact (add_le_add (le_refl (y t)) (mul_le_mul_of_nonneg_left hmon hν.le)).trans hvalue

/-- An integrated order-two bound on each positive-time interval forces
uniform bounds at every integer order, for the original Galerkin equation. -/
theorem GALERKIN_POSITIVE_TIME_ALL_ORDERS
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field)
    (hseed : ∀ σ T : ℝ, 0 < σ → σ < T →
      ∃ S : ℝ, 0 ≤ S ∧ ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
        (∫ s in σ..T, highOrderEnergy 2 N (g.coeff s)) ≤ S)
    (m : ℕ) :
    ∀ τ T : ℝ, 0 < τ → τ < T →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
        ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
          ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B := by
  induction m with
  | zero =>
      intro τ T hτ hτT
      obtain ⟨S, hS, hb⟩ := hseed (τ / 2) T (by positivity) (by linarith)
      apply critical_positive_time_order_from_integrals ν hν a 0 τ T hτ hτT S S hS hS
        (fun N g => ?_) hb
      apply le_trans _ (hb N g)
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact ((g.highOrderEnergy_continuousOn 0).mono
          (fun s hs => (show 0 ≤ τ / 2 by positivity).trans hs.1)).intervalIntegrable_of_Icc
            (by linarith)
      · exact ((g.highOrderEnergy_continuousOn 2).mono
          (fun s hs => (show 0 ≤ τ / 2 by positivity).trans hs.1)).intervalIntegrable_of_Icc
            (by linarith)
      · intro s _
        exact (highOrderEnergy_le_succ 0 N (g.coeff s)).trans
          (highOrderEnergy_le_succ 1 N (g.coeff s))
  | succ m ih =>
      intro τ T hτ hτT
      obtain ⟨S, hS, h2⟩ := hseed (τ / 2) T (by positivity) (by linarith)
      obtain ⟨Y, hY, hm⟩ := ih (τ / 2) T (by positivity) (by linarith)
      apply critical_positive_time_order_from_integrals ν hν a (m + 1) τ T hτ hτT
        (Y / ν) S (div_nonneg hY hν.le) hS (fun N g => ?_) h2
      apply (le_div_iff₀ hν).mpr
      have hb := hm N g T ⟨by linarith, le_rfl⟩
      have he := highOrderEnergy_nonneg m N (g.coeff T)
      nlinarith

theorem SMALL_DATA_POSITIVE_TIME_ALL_ORDERS
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (m : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B :=
  GALERKIN_POSITIVE_TIME_ALL_ORDERS ν hν
    (fun N => finiteSynthesis N (criticalCoeff 1 a))
    (fun σ T hσ hσT => SMALL_DATA_POSITIVE_TIME_H2_BOUND ν hν a hreal hsmall σ hσ T hσT.le)
    m τ T hτ hτT

end
end SingularClosure
