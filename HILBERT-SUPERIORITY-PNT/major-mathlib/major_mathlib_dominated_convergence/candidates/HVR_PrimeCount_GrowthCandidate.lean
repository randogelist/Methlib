import HVR_PrimeCount_MellinCandidate
import Mathlib.NumberTheory.Chebyshev

noncomputable section
open scoped BigOperators
open Filter Asymptotics HVRPrimeCountMellin HVRPrimeZetaSplit HVRZetaLogDerivative
open HVRPowerCorrectionHolomorphic

/-! Candidate discharge of the Mellin partial-sum growth assumption, using
Mathlib's Chebyshev theta bound. This is not a PNT or a Laplace identity.
The imported theta bound's full proof dependencies require independence review.
No Lean run was performed in preparing this file. -/
namespace HVRPrimeCountGrowth

theorem primeTheta_eq_chebyshev (x : ℝ) :
    primeTheta x = (Chebyshev.theta x : ℂ) := by
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hreal : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoefficient n) =
      Chebyshev.theta x := by
    rw [Chebyshev.theta, ← hset]
    simp only [primeCoefficient, Finset.sum_filter]
  unfold primeTheta
  simp only [primeCoefficientC, ← Complex.ofReal_sum, hreal]

/-- The actual log-prime coefficient partial sums have linear growth. -/
theorem primeCoefficient_partial_sum_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoefficientC k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (Real.log 4)
  apply Filter.Eventually.of_forall
  intro n
  have hs : (∑ k ∈ Finset.Icc 1 n, primeCoefficientC k) =
      (Chebyshev.theta (n : ℝ) : ℂ) := by
    simpa only [primeTheta, Nat.floor_natCast] using primeTheta_eq_chebyshev (n : ℝ)
  rw [hs]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simpa only [Real.rpow_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.theta_nonneg (n : ℝ)),
    abs_of_nonneg hn] using
      (Chebyshev.theta_le_log4_mul_x hn)

/-- Mellin identity with no prime-count growth premise. -/
theorem primeSeries_eq_mul_primeThetaMellin_unconditional
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    HVRPrimeComplex.primeSeries sigma t 1 =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) := by
  exact primeSeries_eq_mul_primeThetaMellin sigma t 1 hsigma (by norm_num) hsigma
    primeCoefficient_partial_sum_isBigO

theorem zeta_log_deriv_eq_primeThetaMellin_add_correction_unconditional
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    -deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) +
        complexCorrection (zetaPoint sigma t) := by
  exact zeta_log_deriv_eq_primeThetaMellin_add_correction sigma t 1 hsigma
    (by norm_num) hsigma primeCoefficient_partial_sum_isBigO

end HVRPrimeCountGrowth
