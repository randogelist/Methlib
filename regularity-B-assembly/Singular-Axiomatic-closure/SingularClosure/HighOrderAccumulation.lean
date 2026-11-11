import SingularClosure.HighOrderEstimate
import SingularClosure.SmoothDatumSobolev
import SingularClosure.StrongSobolevRealization
import SingularClosure.LinearBudget

/-! AX6 yields uniform Galerkin bounds in every integral Sobolev order. -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

theorem GalerkinSolution.highOrderEnergy_initial_le
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (ha : SmoothSigmaZero a) (m : ℕ) :
    highOrderEnergy m N (g.coeff 0) ≤
      ‖smoothDatumSobolev m a ha.smooth ha.periodic‖ ^ 2 := by
  let aₘ := smoothDatumSobolev m a ha.smooth ha.periodic
  have hzero : ∀ i : Fin 3, aₘ.val 0 i = 0 :=
    smoothSigmaZero_fourier_meanZero ha
  have hstate : finiteSobolev m N (g.coeff 0) = torusSobolevCutoff m N aₘ := by
    apply Subtype.ext
    rw [finiteSobolev_coeff, torusSobolevCutoff_eq_galerkinCutoff m N aₘ hzero]
    funext k i
    simp only [cutoffCoeff, g.initial]
    split_ifs <;> rfl
  rw [highOrderEnergy_eq_sobolev_norm_sq, hstate]
  exact pow_le_pow_left₀ (norm_nonneg _) (torusSobolevCutoff_norm_le m N aₘ) 2

/-- The cutoff-independent strong budget controls every higher Sobolev order.
The only analytic admission remains the original AX6 statement. -/
theorem AX6_UNIFORM_HIGH_ORDER_ACCUMULATION (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState m t‖ ^ 2 +
          ν * (∫ s in (0 : ℝ)..t, ‖g.sobolevState (m + 1) s‖ ^ 2) ≤ B := by
  obtain ⟨C, hC, hineq⟩ := GALERKIN_HIGH_ORDER_DIFFERENTIAL_INEQUALITY m
  obtain ⟨S, hS, hstrong⟩ := AX6_UNIFORM_SOBOLEV_NORM_BOUNDS hAX6 ν hν a ha T hT
  let E₀ : ℝ := ‖smoothDatumSobolev m a ha.smooth ha.periodic‖ ^ 2
  let M : ℝ := 2 * ν * T + C / ν * S
  refine ⟨E₀ * Real.exp M, mul_nonneg (sq_nonneg _) (Real.exp_pos _).le, ?_⟩
  intro N hN g
  let y : ℝ → ℝ := fun t => highOrderEnergy m N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (highOrderEnergy (m + 1) N (g.coeff t))
  let d : ℝ → ℝ := fun t => (-2 * ν) *
    (highOrderEnergy (m + 1) N (g.coeff t) - highOrderEnergy m N (g.coeff t)) -
      2 * highOrderNonlinearPower m N (g.coeff t)
  let A : ℝ → ℝ := fun t => 2 * ν + C / ν * highOrderEnergy 2 N (g.coeff t)
  have hy : ContinuousOn y (Icc 0 T) :=
    (g.highOrderEnergy_continuousOn m).mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      (g.highOrderEnergy_continuousOn (m + 1))).mono (fun t ht => ht.1)
  have hE2 : ContinuousOn (fun t => highOrderEnergy 2 N (g.coeff t)) (Icc 0 T) :=
    (g.highOrderEnergy_continuousOn 2).mono (fun t ht => ht.1)
  have hA : ContinuousOn A (Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul hE2)
  have hA_nonneg (t : ℝ) (_ht : t ∈ Icc 0 T) : 0 ≤ A t := by
    exact add_nonneg (mul_nonneg (by norm_num) hν.le)
      (mul_nonneg (div_nonneg hC.le hν.le) (highOrderEnergy_nonneg _ _ _))
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt y (d t) t :=
    (g.highOrderEnergy_balance m ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have hlinear (t : ℝ) (ht : t ∈ Ioo 0 T) :
      d t + ν * (z t) ^ 2 ≤ A t * y t := by
    obtain ⟨d', hd', hb⟩ := hineq ν hν a N g t ht.1.le
    have heq : d t = d' := (hderiv t ht).unique
      (hd'.hasDerivAt (Ici_mem_nhds ht.1))
    dsimp only [z]
    rw [Real.sq_sqrt (highOrderEnergy_nonneg _ _ _), heq]
    exact hb
  have hbudget : (∫ s in (0 : ℝ)..T, A s) ≤ M := by
    obtain ⟨_, hi2, h2, _, _⟩ := hstrong N hN g
    have hiE2 : IntervalIntegrable (fun t => highOrderEnergy 2 N (g.coeff t)) volume 0 T :=
      hE2.intervalIntegrable_of_Icc hT.le
    have h2' : (∫ t in (0 : ℝ)..T, highOrderEnergy 2 N (g.coeff t)) ≤ S := by
      simpa only [highOrderEnergy_eq_sobolev_norm_sq, GalerkinSolution.sobolevState] using h2
    dsimp only [A, M]
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      (hiE2.const_mul (C / ν)), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul]
    simp only [sub_zero, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2' (div_nonneg hC.le hν.le)]
  have hb := LINEAR_ENERGY_OF_COEFFICIENT_BUDGET hν.le hT.le hy hz hA
    (fun t _ => highOrderEnergy_nonneg _ _ _) hA_nonneg
    (g.highOrderEnergy_initial_le ha m) hderiv hlinear hbudget
  intro t ht
  have hzsq (s : ℝ) : (z s) ^ 2 = highOrderEnergy (m + 1) N (g.coeff s) :=
    Real.sq_sqrt (highOrderEnergy_nonneg _ _ _)
  simpa only [hzsq, highOrderEnergy_eq_sobolev_norm_sq,
    GalerkinSolution.sobolevState] using hb t ht

end

end SingularClosure
