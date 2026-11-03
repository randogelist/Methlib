import HVR_PrimeCount_GrowthCandidate
import HVR_Smoothing_AnalyticGerms

noncomputable section
open scoped BigOperators
open Filter Asymptotics
open HVRPrimeZetaSplit HVRPowerCorrectionHolomorphic
open HVRPrimeCountMellin HVRSmoothingAnalyticGerms

/-!
The actual prime-count Mellin integral, under the explicit growth hypothesis,
coincides after pole subtraction with the raw analytic germ. The exponential
change of variables and the growth hypothesis are not proved in this file.
No local Lean run was performed.
-/
namespace HVRPrimeCountMellinGerm

theorem primeThetaMellin_sub_pole_eq_regularPartAt
    (sigma t r : ℝ) (hsigma : 1 < sigma) (hr : 0 ≤ r) (hrs : r < sigma)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoefficientC k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    primeThetaMellin (zetaPoint sigma t) - (zetaPoint sigma t - 1)⁻¹ =
      regularPartAt (zetaPoint sigma t) := by
  have hs : zetaPoint sigma t ≠ 0 := by
    intro heq
    have hreal : (zetaPoint sigma t).re = sigma := by simp [zetaPoint]
    rw [heq] at hreal
    simp only [Complex.zero_re] at hreal
    linarith
  have h := zeta_log_deriv_eq_primeThetaMellin_add_correction
    sigma t r hsigma hr hrs hO
  have hquot :
      (-deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) -
        complexCorrection (zetaPoint sigma t)) / zetaPoint sigma t =
      primeThetaMellin (zetaPoint sigma t) := by
    rw [h]
    field_simp [hs] <;> ring
  unfold regularPartAt
  rw [hquot]

/-- The same connection using the candidate linear bound for the actual
prime-coefficient partial sums. -/
theorem primeThetaMellin_sub_pole_eq_regularPartAt_of_growth
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    primeThetaMellin (zetaPoint sigma t) - (zetaPoint sigma t - 1)⁻¹ =
      regularPartAt (zetaPoint sigma t) := by
  exact primeThetaMellin_sub_pole_eq_regularPartAt sigma t 1 hsigma
    (by norm_num) hsigma HVRPrimeCountGrowth.primeCoefficient_partial_sum_isBigO

end HVRPrimeCountMellinGerm
