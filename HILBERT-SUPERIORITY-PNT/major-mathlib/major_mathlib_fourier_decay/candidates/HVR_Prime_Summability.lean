import HVR_Prime_Gram
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

noncomputable section

/-!
Prime-only weights as a series over natural numbers.  This module establishes
summability in the half-plane sigma > 1 by comparison with a p-series; it
contains no zeta zero-free theorem, Tauberian argument, or PNT assertion.
-/
namespace HVRPrimeSummability

/-- The terms are zero at every nonprime, including 0 and 1. -/
def primeWeightSeries (sigma : ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime n then HVRPrimeGram.primeWeight sigma n else 0

theorem primeWeightSeries_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ primeWeightSeries sigma n := by
  by_cases hp : Nat.Prime n
  · simp only [primeWeightSeries, hp, if_true]
    exact HVRPrimeGram.primeWeight_nonneg sigma hp
  · simp [primeWeightSeries, hp]

/-- For every sigma > 1 the exact prime-weight series is summable.
The input is only the elementary real p-series and logarithmic power bound. -/
theorem primeWeightSeries_summable (sigma : ℝ) (hsigma : 1 < sigma) :
    Summable (primeWeightSeries sigma) := by
  let ε : ℝ := (sigma - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexponent : ε - sigma < -1 := by dsimp [ε]; linarith
  have hpseries : Summable (fun n : ℕ => (n : ℝ) ^ (ε - sigma)) :=
    Real.summable_nat_rpow.mpr hexponent
  have hmajorant : Summable (fun n : ℕ => (n : ℝ) ^ (ε - sigma) / ε) :=
    hpseries.div_const ε
  refine Summable.of_nonneg_of_le (primeWeightSeries_nonneg sigma) ?_ hmajorant
  intro n
  by_cases hp : Nat.Prime n
  · have hn : 0 < (n : ℝ) := by exact_mod_cast hp.pos
    have hexp : Real.exp (-sigma * Real.log (n : ℝ)) = (n : ℝ) ^ (-sigma) := by
      rw [Real.rpow_def_of_pos hn]
      congr 1
      ring
    simp only [primeWeightSeries, hp, if_true, HVRPrimeGram.primeWeight, hexp]
    calc
      Real.log (n : ℝ) * (n : ℝ) ^ (-sigma) ≤
          ((n : ℝ) ^ ε / ε) * (n : ℝ) ^ (-sigma) :=
        mul_le_mul_of_nonneg_right (Real.log_natCast_le_rpow_div n hε)
          (Real.rpow_nonneg (le_of_lt hn) _)
      _ = (n : ℝ) ^ (ε - sigma) / ε := by
        rw [show ε - sigma = ε + (-sigma) by ring, Real.rpow_add hn]
        ring
  · simp only [primeWeightSeries, hp, if_false]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (le_of_lt hε)

end HVRPrimeSummability
