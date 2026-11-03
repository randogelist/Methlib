import HVR_Zeta_CorrectionIdentity
import Mathlib.NumberTheory.LSeries.SumCoeff

noncomputable section
open scoped BigOperators
open Filter Asymptotics
open HVRPrimeZetaSplit HVRZetaLogDerivative
open HVRPowerCorrectionHolomorphic HVRZetaCorrectionIdentity

/-!
Candidate prime-count Mellin bridge.  The coefficient function is the
actual log-prime coefficient from the already audited zeta split.  The
partial-sum growth hypothesis is explicit and is NOT discharged here; neither
the exponential change of variables nor a Laplace-transform identity is
claimed. The imported Mathlib integral theorem and all transitive dependencies
still require route-independence review. This source has not been compiled.
-/
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

/-- Partial summation for the actual prime series, conditional on its stated
elementary partial-sum growth bound. -/
theorem primeSeries_eq_mul_primeThetaMellin (sigma t r : ℝ)
    (hsigma : 1 < sigma) (hr : 0 ≤ r) (hrs : r < sigma)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoefficientC k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    HVRPrimeComplex.primeSeries sigma t 1 =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) := by
  have hrs' : r < (zetaPoint sigma t).re := by
    simpa [zetaPoint] using hrs
  have h := LSeries_eq_mul_integral primeCoefficientC hr hrs'
    (prime_lseries_summable sigma t hsigma) hO
  rw [prime_lseries_eq_primeSeries] at h
  simpa [primeThetaMellin, primeTheta] using h

/-- The audited zeta/prime correction identity, now expressed through the
prime-count Mellin integral under the same explicit growth hypothesis. -/
theorem zeta_log_deriv_eq_primeThetaMellin_add_correction (sigma t r : ℝ)
    (hsigma : 1 < sigma) (hr : 0 ≤ r) (hrs : r < sigma)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoefficientC k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    -deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) +
        complexCorrection (zetaPoint sigma t) := by
  rw [zeta_log_deriv_eq_primeSeries_add_complexCorrection sigma t hsigma,
      primeSeries_eq_mul_primeThetaMellin sigma t r hsigma hr hrs hO]

end HVRPrimeCountMellin
