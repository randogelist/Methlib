import HVR_Prime_InfiniteGram
import Mathlib.NumberTheory.LSeries.Dirichlet

noncomputable section

/-!
Open-half-plane bridge to the actual Riemann zeta function. This module uses
Mathlib's pre-existing von Mangoldt L-series logarithmic-derivative theorem.
The arithmetic coefficient split is pointwise: it does not prove convergence
or holomorphic continuation of the higher-prime-power correction, does not
identify the first part with the preceding HVR real cosine sum, and does not
prove boundary zero-freeness or PNT.
-/
namespace HVRZetaLogDerivative

/-- Coefficient on the primes, zero elsewhere. -/
def primeCoefficient (n : ℕ) : ℝ :=
  if Nat.Prime n then Real.log (n : ℝ) else 0

/-- Coefficient difference from the full von Mangoldt function. -/
def higherCoefficient (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n - primeCoefficient n

/-- Exact coefficient-level decomposition; this alone says nothing about
summability, reindexing, or analytic continuation. -/
theorem vonMangoldt_coefficient_split (n : ℕ) :
    ArithmeticFunction.vonMangoldt n = primeCoefficient n + higherCoefficient n := by
  simp only [higherCoefficient]
  ring

/-- No higher correction occurs at a prime. -/
theorem higherCoefficient_eq_zero_of_prime {p : ℕ} (hp : Nat.Prime p) :
    higherCoefficient p = 0 := by
  simp [higherCoefficient, primeCoefficient, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Outside prime powers the higher correction vanishes. -/
theorem higherCoefficient_eq_zero_of_not_prime_pow {n : ℕ}
    (hn : ¬ IsPrimePow n) : higherCoefficient n = 0 := by
  have hnprime : ¬ Nat.Prime n := fun hp => hn hp.isPrimePow
  have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  simp [higherCoefficient, primeCoefficient, hnprime, hzero]

/-- Nonzero higher coefficients are supported on composite prime powers. -/
theorem higherCoefficient_support {n : ℕ} (hn : higherCoefficient n ≠ 0) :
    IsPrimePow n ∧ ¬ Nat.Prime n := by
  constructor
  · by_contra h
    exact hn (higherCoefficient_eq_zero_of_not_prime_pow h)
  · intro hp
    exact hn (higherCoefficient_eq_zero_of_prime hp)

/-- The von Mangoldt coefficient at a positive power of a prime. -/
theorem vonMangoldt_at_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    ArithmeticFunction.vonMangoldt (p ^ k) = Real.log (p : ℝ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- The actual zeta log-derivative bridge on Re(s) > 1. The proof is the
named Mathlib theorem. It does not by itself split off the prime series. -/
theorem vonMangoldt_series_eq_zeta_log_deriv {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s := by
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

end HVRZetaLogDerivative

#check HVRZetaLogDerivative.vonMangoldt_coefficient_split
#print axioms HVRZetaLogDerivative.vonMangoldt_coefficient_split
#check HVRZetaLogDerivative.higherCoefficient_eq_zero_of_prime
#print axioms HVRZetaLogDerivative.higherCoefficient_eq_zero_of_prime
#check HVRZetaLogDerivative.higherCoefficient_eq_zero_of_not_prime_pow
#print axioms HVRZetaLogDerivative.higherCoefficient_eq_zero_of_not_prime_pow
#check HVRZetaLogDerivative.higherCoefficient_support
#print axioms HVRZetaLogDerivative.higherCoefficient_support
#check HVRZetaLogDerivative.vonMangoldt_at_prime_pow
#print axioms HVRZetaLogDerivative.vonMangoldt_at_prime_pow
#check HVRZetaLogDerivative.vonMangoldt_series_eq_zeta_log_deriv
#print axioms HVRZetaLogDerivative.vonMangoldt_series_eq_zeta_log_deriv
