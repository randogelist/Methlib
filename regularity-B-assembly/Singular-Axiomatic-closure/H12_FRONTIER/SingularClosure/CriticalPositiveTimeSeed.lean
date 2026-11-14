import SingularClosure.CriticalPositiveTimeScalar
import SingularClosure.SmallDataAX6Closure
import SingularClosure.StrongAccumulation
import SingularClosure.StrongSobolevRealization
import SingularClosure.HighOrderGalerkin

/-! The actual H1/H2 positive-time seed for rough critical data. The initial
enstrophy is selected from its proved square budget; it is never assumed
uniform at time zero. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

theorem SMALL_DATA_POSITIVE_TIME_ENSTROPHY_ACCUMULATION
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L := by
  obtain ⟨C, hC, hineq⟩ := GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY
  let M : ℝ := ‖a‖ ^ 4 / (4 * (ν - criticalNonlinearConstant * ‖a‖))
  let κ : ℝ := C / ν ^ 3
  have hM : 0 ≤ M := div_nonneg (pow_nonneg (norm_nonneg a) 4)
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
  have hκ : 0 ≤ κ := div_nonneg hC.le (pow_nonneg hν.le 3)
  have hT : 0 ≤ T := hτ.le.trans hτT
  refine ⟨Real.sqrt (M / τ) * Real.exp (κ * M),
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le, ?_⟩
  intro N g
  let y : ℝ → ℝ := fun t => coefficientDissipation N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (coefficientLaplacianSquare N (g.coeff t))
  let d : ℝ → ℝ := fun t => coefficientEnstrophyRate ν N (g.coeff t)
  have hy : ContinuousOn y (Icc 0 T) :=
    g.coefficientDissipation_continuousOn.mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      g.coefficientLaplacianSquare_continuousOn).mono (fun t ht => ht.1)
  have hd : ContinuousOn d (Icc 0 T) :=
    g.coefficientEnstrophyRate_continuousOn.mono (fun t ht => ht.1)
  have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t := by
    intro t ht
    exact (g.coefficientDissipation_hasDerivWithinAt ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)
  have hcubic : ∀ t ∈ Ioo 0 T,
      d t + ν * z t ^ 2 ≤ κ * y t ^ 3 := by
    intro t ht
    obtain ⟨d', hd', hb⟩ := hineq ν hν _ N g t ht.1.le
    have heq : d t = d' := (hderiv t ht).unique
      (hd'.hasDerivAt (Ici_mem_nhds ht.1))
    dsimp only [z]
    rw [Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff t)), heq]
    exact hb
  have hbudget : (∫ t in (0 : ℝ)..T, y t ^ 2) ≤ M :=
    g.critical_square_budget_of_differential_inequality hT criticalNonlinearConstant_pos.le
      (norm_nonneg a) hsmall (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
      (fun t ht => g.critical_differential_inequality ht.1)
  have hacc := CUBIC_POSITIVE_TIME_ACCUMULATION hν hκ hτ hτT hM hy hz hd
    (fun t _ => coefficientDissipation_nonneg N (g.coeff t)) hderiv hcubic hbudget
  have hzsq (s : ℝ) : z s ^ 2 = coefficientLaplacianSquare N (g.coeff s) :=
    Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff s))
  intro t ht
  simpa only [y, hzsq] using hacc t ht

theorem SMALL_DATA_POSITIVE_TIME_H2_BOUND
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
        (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤ S := by
  obtain ⟨L, hL, hacc⟩ := SMALL_DATA_POSITIVE_TIME_ENSTROPHY_ACCUMULATION
    ν hν a hreal hsmall τ hτ T hτT
  refine ⟨3 * L * (T - τ) + L / ν,
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sub_nonneg.mpr hτT))
      (div_nonneg hL hν.le), ?_⟩
  intro N g
  have hy (t : ℝ) (ht : t ∈ Icc τ T) : coefficientDissipation N (g.coeff t) ≤ L := by
    have h := hacc N g t ht
    have hz : 0 ≤ ∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s) :=
      intervalIntegral.integral_nonneg_of_forall ht.1
        (fun s => coefficientLaplacianSquare_nonneg N (g.coeff s))
    nlinarith [mul_nonneg hν.le hz]
  have hZi : IntervalIntegrable (fun t => coefficientLaplacianSquare N (g.coeff t))
      volume τ T :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun t ht => hτ.le.trans ht.1)).intervalIntegrable_of_Icc hτT
  have hZ : (∫ t in τ..T, coefficientLaplacianSquare N (g.coeff t)) ≤ L / ν := by
    apply (le_div_iff₀ hν).2
    have h := hacc N g T ⟨hτT, le_rfl⟩
    nlinarith [coefficientDissipation_nonneg N (g.coeff T)]
  have hH2i : IntervalIntegrable (fun t => highOrderEnergy 2 N (g.coeff t)) volume τ T :=
    ((g.highOrderEnergy_continuousOn 2).mono
      (fun t ht => hτ.le.trans ht.1)).intervalIntegrable_of_Icc hτT
  have hpoint (t : ℝ) (ht : t ∈ Icc τ T) :
      highOrderEnergy 2 N (g.coeff t) ≤ 3 * L + coefficientLaplacianSquare N (g.coeff t) := by
    have ht0 : 0 ≤ t := hτ.le.trans ht.1
    have heq : highOrderEnergy 2 N (g.coeff t) =
        coefficientEnergy N (g.coeff t) + 2 * coefficientDissipation N (g.coeff t) +
          coefficientLaplacianSquare N (g.coeff t) := by
      rw [highOrderEnergy_eq_sobolev_norm_sq]
      change ‖g.sobolevState 2 t‖ ^ 2 = _
      rw [g.sobolevState_H2_square_eq ht0, g.physicalH2Square_eq ht0]
    rw [heq]
    have henergy := coefficientEnergy_le_dissipation N (g.coeff t)
    linarith [hy t ht]
  calc
    _ ≤ ∫ t in τ..T, 3 * L + coefficientLaplacianSquare N (g.coeff t) :=
      intervalIntegral.integral_mono_on hτT hH2i (intervalIntegrable_const.add hZi) hpoint
    _ = (T - τ) * (3 * L) + ∫ t in τ..T, coefficientLaplacianSquare N (g.coeff t) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
        intervalIntegral.integral_const]
      rfl
    _ ≤ (T - τ) * (3 * L) + L / ν := add_le_add (le_refl _) hZ
    _ = _ := by ring

end SingularClosure
