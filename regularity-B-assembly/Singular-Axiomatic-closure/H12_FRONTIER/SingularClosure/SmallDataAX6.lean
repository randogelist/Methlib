import SingularClosure.CriticalInitialEnergy
import SingularClosure.CriticalInvariant
import SingularClosure.CriticalDissipation
import SingularClosure.Ax6ExactBudget

/-!
# Datumwise AX6 for the actual rough-data Galerkin family

The datumwise proposition quantifies the original finite trajectories with
their actual Fourier-cutoff initial data. The scalar-to-physical conversion
below is an intermediate implication, not an assumed nonlinear estimate.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval NNReal ENNReal

namespace SingularClosure

/-- Datumwise AX6 for a literal critical Fourier datum. This does not assert
the universal AX6 statement for arbitrary smooth initial data. -/
def CriticalDatumAX6 (ν : ℝ) (a : CriticalSobolev 1) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ M : ℝ≥0,
    ∀ N : ℕ, 1 ≤ N →
    ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      budget6 N g.coeff T ≤ (M : ℝ≥0∞)

/-- The proved scalar sharp budget, applied to the original finite ODE.
The sole differential hypothesis is stated explicitly and is not bundled
as an unresolved closure certificate. -/
theorem GalerkinSolution.critical_square_budget_of_differential_inequality
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {C a₀ T : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hinit : criticalEnergy 1 N (g.coeff 0) ≤ a₀ ^ 2)
    (hcritical : ∀ t ∈ Ico 0 T,
      criticalEnergyRate ν 1 N (g.coeff t) +
        2 * (ν - C * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
          criticalEnergy 3 N (g.coeff t) ≤ 0) :
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) ^ 2) ≤
      a₀ ^ 4 / (4 * (ν - C * a₀)) := by
  have h := CRITICAL_SQUARE_BUDGET_DIV
    (A := fun t => criticalEnergy 1 N (g.coeff t))
    (B := fun t => criticalEnergy 3 N (g.coeff t))
    (X := fun t => criticalEnergy 2 N (g.coeff t))
    (d := fun t => criticalEnergyRate ν 1 N (g.coeff t))
    hT hC ha₀ hsmall
    ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 2).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t)) hinit
    (fun t ht => g.criticalEnergy_balance 1 ht.1) hcritical
    (fun t _ => criticalEnergy_interpolation N (g.coeff t))
  have hden : 0 ≤ 4 * (ν - C * a₀) :=
    mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le
  have hterminal :
      (a₀ ^ 4 - criticalEnergy 1 N (g.coeff T) ^ 2) / (4 * (ν - C * a₀)) ≤
        a₀ ^ 4 / (4 * (ν - C * a₀)) :=
    div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) hden
  simpa only [criticalEnergy_two_eq_coefficientDissipation] using h.trans hterminal

/-- Exact conversion to the six-channel ENNReal integral, without any
reconstruction loss or cutoff-dependent constant. -/
theorem GalerkinSolution.critical_budget6_of_differential_inequality
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {C a₀ T : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hinit : criticalEnergy 1 N (g.coeff 0) ≤ a₀ ^ 2)
    (hcritical : ∀ t ∈ Ico 0 T,
      criticalEnergyRate ν 1 N (g.coeff t) +
        2 * (ν - C * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
          criticalEnergy 3 N (g.coeff t) ≤ 0) :
    budget6 N g.coeff T ≤ ENNReal.ofReal (a₀ ^ 4 / (4 * (ν - C * a₀))) := by
  rw [g.budget6_eq_ofReal_intervalIntegral hT]
  exact ENNReal.ofReal_le_ofReal
    (g.critical_square_budget_of_differential_inequality hT hC ha₀ hsmall hinit hcritical)

/-- Algebraic passage from the physical critical nonlinear estimate to
the actual differential inequality. No estimate is asserted by this lemma. -/
theorem criticalEnergyRate_inequality_of_nonlinear_bound
    {ν C : ℝ} {N : ℕ} {c : FourierCoeff}
    (hbound : |criticalNonlinearPower 1 N c| ≤
      C * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c) :
    criticalEnergyRate ν 1 N c +
      2 * (ν - C * Real.sqrt (criticalEnergy 1 N c)) * criticalEnergy 3 N c ≤ 0 := by
  have hlower := (abs_le.mp hbound).1
  unfold criticalEnergyRate
  norm_num only [Nat.reduceAdd]
  nlinarith only [hlower]

end SingularClosure
