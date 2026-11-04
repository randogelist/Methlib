import HVR_Zeta_CorrectionIdentity
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open HVRPrimeZetaSplit HVRZetaLogDerivative

/-! Definitions and the coefficient identification moved upstream unchanged
from HVR_PrimeCount_MellinCandidate. This source is a candidate refactor.
No local Lean run was performed. -/
namespace HVRPrimeCountMellin

/-- Complex-valued logarithmic prime count up to a real threshold. -/
def primeTheta (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoefficientC n

/-- The Mellin integral of the actual logarithmic prime count. -/
def primeThetaMellin (s : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 1, primeTheta x * (x : ℂ) ^ (-(s + 1))

theorem primeTheta_eq_log_prime_sum (x : ℝ) :
    primeTheta x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        if Nat.Prime n then (Real.log (n : ℝ) : ℂ) else 0 := by
  unfold primeTheta
  apply Finset.sum_congr rfl
  intro n hn
  change ((if Nat.Prime n then Real.log (n : ℝ) else 0 : ℝ) : ℂ) =
    (if Nat.Prime n then (Real.log (n : ℝ) : ℂ) else 0)
  by_cases hp : Nat.Prime n <;>
    simp only [hp, if_true, if_false, Complex.ofReal_zero]

end HVRPrimeCountMellin
