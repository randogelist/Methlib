import HVR_Prime_ZetaSplit
import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section

/-!
Candidate arithmetic reindexing of the already established higher-coefficient
L-series. This does not yet evaluate the inner sums as geometric series and
does not prove their equality to the complex correction function. No local
Lean run has been performed.
-/
namespace HVRHigherCoefficientReindex

open HVRZetaLogDerivative HVRPrimeZetaSplit

/-- Each nonzero higher-coefficient L-series term is supported on a prime
power. The stronger fact that its support excludes primes is used below. -/
theorem higher_lseries_support_prime_powers (s : ℂ) :
    Function.support (LSeries.term higherCoefficientC s) ⊆
      {n : ℕ | IsPrimePow n} := by
  intro n hn
  change LSeries.term higherCoefficientC s n ≠ 0 at hn
  have hc : higherCoefficient n ≠ 0 := by
    intro hz
    apply hn
    simp [LSeries.term_def, higherCoefficientC, hz]
  exact (higherCoefficient_support hc).1

/-- The higher-coefficient term vanishes at every prime. -/
theorem higher_lseries_term_at_prime (s : ℂ) (p : Nat.Primes) :
    LSeries.term higherCoefficientC s (p : ℕ) = 0 := by
  simp [LSeries.term_def, higherCoefficientC,
    higherCoefficient_eq_zero_of_prime p.property]

/-- Absolute convergence allows the actual coefficient series to be
reindexed as a sum over prime powers of exponent at least two. -/
theorem higher_lseries_eq_prime_power_tsum (sigma t : ℝ) (hsigma : 1 < sigma) :
    LSeries higherCoefficientC (zetaPoint sigma t) =
      ∑' p : Nat.Primes, ∑' k : ℕ,
        LSeries.term higherCoefficientC (zetaPoint sigma t) ((p : ℕ) ^ (k + 2)) := by
  have hsum : Summable (LSeries.term higherCoefficientC (zetaPoint sigma t)) := by
    exact higher_lseries_summable sigma t hsigma
  have hprime : (∑' p : Nat.Primes,
      LSeries.term higherCoefficientC (zetaPoint sigma t) (p : ℕ)) = 0 := by
    calc
      (∑' p : Nat.Primes, LSeries.term higherCoefficientC (zetaPoint sigma t) (p : ℕ)) =
          ∑' _p : Nat.Primes, (0 : ℂ) := by
        apply tsum_congr
        intro p
        exact higher_lseries_term_at_prime (zetaPoint sigma t) p
      _ = 0 := tsum_zero
  have hreindex := tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers
    hsum (higher_lseries_support_prime_powers (zetaPoint sigma t))
  change (∑' n : ℕ, LSeries.term higherCoefficientC (zetaPoint sigma t) n) = _
  rw [hreindex, hprime, zero_add]

end HVRHigherCoefficientReindex
