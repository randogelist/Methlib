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
  let f := LSeries.term higherCoefficientC (zetaPoint sigma t)
  have hsum : Summable f := higher_lseries_summable sigma t hsigma
  have hsupport : Function.support f ⊆ {n : ℕ | IsPrimePow n} :=
    higher_lseries_support_prime_powers (zetaPoint sigma t)
  have hsub : Summable (fun n : {n : ℕ // IsPrimePow n} => f n.1) :=
    hsum.subtype _
  -- The native regrouping argument uses the prime-base/exponent equivalence.
  -- Adapted from HVRNativePrimePowerRegroup and Mathlib/NumberTheory/EulerProduct/Basic.lean,
  -- copyright (c) 2023 Michael Stoll, Apache License 2.0.
  have hindex :
      (∑' (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 1))) =
        ∑' n : {n : ℕ // IsPrimePow n}, f n.1 := by
    calc
      _ = ∑' pk : Nat.Primes × ℕ, f (Nat.Primes.prodNatEquiv pk) := by
        simpa using (hsub.comp_injective Nat.Primes.prodNatEquiv.injective).tsum_prod.symm
      _ = _ := by rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv]
  change (∑' n : ℕ, f n) = ∑' (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k + 2))
  rw [← tsum_subtype_eq_of_support_subset hsupport, ← hindex]
  apply tsum_congr
  intro p
  have hfiber : Summable (fun k : ℕ => f ((p : ℕ) ^ (k + 1))) :=
    hsum.comp_injective <| (strictMono_nat_of_lt_succ
      (pow_lt_pow_right₀ p.property.one_lt <| lt_add_one <| · + 1)).injective
  have hp : f (p : ℕ) = 0 := higher_lseries_term_at_prime (zetaPoint sigma t) p
  simpa only [zero_add, pow_one, hp] using hfiber.tsum_eq_zero_add

end HVRHigherCoefficientReindex
