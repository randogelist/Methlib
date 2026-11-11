import SingularClosure.SmallDataAX6
import SingularClosure.CriticalNonlinear

/-! Unconditional datumwise AX6 under the strict critical smallness condition.
The universal nonlinear constant is selected from a proved physical estimate.
No analytic bound, invariant, or budget remains a hypothesis of this endpoint. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped Interval NNReal ENNReal

namespace SingularClosure

def criticalNonlinearConstant : ℝ := FINITE_CRITICAL_NONLINEAR_BOUND.choose

theorem criticalNonlinearConstant_pos : 0 < criticalNonlinearConstant :=
  FINITE_CRITICAL_NONLINEAR_BOUND.choose_spec.1

theorem criticalNonlinearConstant_bound (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    |criticalNonlinearPower 1 N c| ≤
      criticalNonlinearConstant * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  FINITE_CRITICAL_NONLINEAR_BOUND.choose_spec.2 N c hsupp hreal hsol

theorem GalerkinSolution.critical_differential_inequality
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    criticalEnergyRate ν 1 N (g.coeff t) +
      2 * (ν - criticalNonlinearConstant * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
        criticalEnergy 3 N (g.coeff t) ≤ 0 :=
  criticalEnergyRate_inequality_of_nonlinear_bound
    (criticalNonlinearConstant_bound N (g.coeff t)
      (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht))

theorem criticalGalerkin_energy_invariant
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  CRITICAL_ENERGY_INVARIANT hT criticalNonlinearConstant_pos.le (norm_nonneg a)
    hsmall ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => g.critical_differential_inequality ht.1)

theorem criticalGalerkin_dissipation_budget
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) + 2 * (ν - criticalNonlinearConstant * ‖a‖) *
        (∫ s in (0 : ℝ)..t, criticalEnergy 3 N (g.coeff s)) ≤ ‖a‖ ^ 2 :=
  CRITICAL_DISSIPATION_BUDGET hT criticalNonlinearConstant_pos.le (norm_nonneg a)
    hsmall ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 3).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => g.critical_differential_inequality ht.1)

/-- The terminal-energy form retains the exact factor four. -/
theorem criticalGalerkin_sharp_square_budget
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) ^ 2) ≤
      (‖a‖ ^ 4 - criticalEnergy 1 N (g.coeff T) ^ 2) /
        (4 * (ν - criticalNonlinearConstant * ‖a‖)) := by
  have h := CRITICAL_SQUARE_BUDGET_DIV
    (A := fun t => criticalEnergy 1 N (g.coeff t))
    (B := fun t => criticalEnergy 3 N (g.coeff t))
    (X := fun t => criticalEnergy 2 N (g.coeff t))
    (d := fun t => criticalEnergyRate ν 1 N (g.coeff t))
    hT criticalNonlinearConstant_pos.le (norm_nonneg a) hsmall
    ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 2).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => g.critical_differential_inequality ht.1)
    (fun t _ => criticalEnergy_interpolation N (g.coeff t))
  simpa only [criticalEnergy_two_eq_coefficientDissipation] using h

/-- Exact physical six-channel budget, uniform in time and Fourier cutoff. -/
theorem SMALL_DATA_SIX_CHANNEL_BUDGET
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    budget6 N g.coeff T ≤
      ENNReal.ofReal (‖a‖ ^ 4 / (4 * (ν - criticalNonlinearConstant * ‖a‖))) :=
  g.critical_budget6_of_differential_inequality hT criticalNonlinearConstant_pos.le
    (norm_nonneg a) hsmall (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.critical_differential_inequality ht.1)

/-- Datumwise AX6 is discharged from critical smallness. This theorem does
not discharge the universal AX6 premise for arbitrary smooth data. -/
theorem SMALL_DATA_AX6
    (ν : ℝ) (_hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (_hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (_hzero : SpectralMeanZero (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a := by
  intro T hT
  let M : ℝ := ‖a‖ ^ 4 / (4 * (ν - criticalNonlinearConstant * ‖a‖))
  have hM : 0 ≤ M :=
    div_nonneg (pow_nonneg (norm_nonneg a) 4)
      (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
  refine ⟨Real.toNNReal M, ?_⟩
  intro N _ g
  change budget6 N g.coeff T ≤ ENNReal.ofReal M
  exact SMALL_DATA_SIX_CHANNEL_BUDGET a hreal hsmall hT.le g

end SingularClosure
