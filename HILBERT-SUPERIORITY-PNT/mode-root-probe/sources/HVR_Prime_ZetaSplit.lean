import HVR_Prime_Complex
import HVR_Zeta_LogDerivative
import Mathlib.NumberTheory.LSeries.Linearity

open scoped BigOperators
noncomputable section

/-!
A candidate, concrete split of the von Mangoldt L-series into the
already-audited complex prime series plus the L-series of the coefficient
correction, in the open half-plane sigma > 1. No analyticity or
identification of that correction with the resummed prime-power expression
is asserted here. The Mathlib von Mangoldt/zeta identity is used explicitly.
-/
namespace HVRPrimeZetaSplit

open HVRPrimeComplex HVRZetaLogDerivative

def primeCoefficientC (n : ℕ) : ℂ := (primeCoefficient n : ℂ)
def higherCoefficientC (n : ℕ) : ℂ := (higherCoefficient n : ℂ)
def vonMangoldtC (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

def zetaPoint (sigma t : ℝ) : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I

/-- This is an equality of coefficient functions, not a convergence claim. -/
theorem higherCoefficientC_eq_sub :
    higherCoefficientC = vonMangoldtC - primeCoefficientC := by
  funext n
  simp [higherCoefficientC, vonMangoldtC, primeCoefficientC, higherCoefficient]

theorem primeCoefficientC_zero : primeCoefficientC 0 = 0 := by
  simp [primeCoefficientC, primeCoefficient]

/-- The exact terms of Mathlib's L-series match the previously certified
complex prime-phase terms. -/
theorem prime_lseries_term_eq (sigma t : ℝ) (n : ℕ) :
    LSeries.term primeCoefficientC (zetaPoint sigma t) n =
      primeTerm sigma t 1 n := by
  rw [LSeries.term_def₀ primeCoefficientC_zero]
  rw [primeTerm_eq_dirichlet_indicator]
  by_cases hp : Nat.Prime n
  · simp [primeCoefficientC, primeCoefficient, hp, zetaPoint]
  · simp [primeCoefficientC, primeCoefficient, hp]

/-- The prime L-series is exactly the HVR complex prime sum. -/
theorem prime_lseries_eq_primeSeries (sigma t : ℝ) :
    LSeries primeCoefficientC (zetaPoint sigma t) = primeSeries sigma t 1 := by
  unfold LSeries primeSeries
  apply tsum_congr
  intro n
  exact prime_lseries_term_eq sigma t n

theorem prime_lseries_summable (sigma t : ℝ) (hsigma : 1 < sigma) :
    LSeriesSummable primeCoefficientC (zetaPoint sigma t) := by
  change Summable (LSeries.term primeCoefficientC (zetaPoint sigma t))
  have hfun : LSeries.term primeCoefficientC (zetaPoint sigma t) =
      primeTerm sigma t 1 := funext (prime_lseries_term_eq sigma t)
  rw [hfun]
  exact primeTerm_summable sigma t 1 hsigma

/-- The correction series is genuinely summable for sigma > 1. -/
theorem higher_lseries_summable (sigma t : ℝ) (hsigma : 1 < sigma) :
    LSeriesSummable higherCoefficientC (zetaPoint sigma t) := by
  rw [higherCoefficientC_eq_sub]
  apply LSeriesSummable.sub
  · apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    simpa [zetaPoint] using hsigma
  · exact prime_lseries_summable sigma t hsigma

/-- The actual zeta log derivative is the prime-only HVR series plus the
L-series of the coefficient correction, for real sigma > 1 and real t. -/
theorem zeta_log_deriv_eq_primeSeries_add_higher (sigma t : ℝ)
    (hsigma : 1 < sigma) :
    -deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) =
      primeSeries sigma t 1 + LSeries higherCoefficientC (zetaPoint sigma t) := by
  have hv : LSeriesSummable vonMangoldtC (zetaPoint sigma t) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    simpa [zetaPoint] using hsigma
  have hp := prime_lseries_summable sigma t hsigma
  have hz : LSeries vonMangoldtC (zetaPoint sigma t) =
      -deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) := by
    apply vonMangoldt_series_eq_zeta_log_deriv
    simpa [zetaPoint] using hsigma
  rw [higherCoefficientC_eq_sub, LSeries_sub hv hp, prime_lseries_eq_primeSeries]
  rw [hz]
  ring

end HVRPrimeZetaSplit
