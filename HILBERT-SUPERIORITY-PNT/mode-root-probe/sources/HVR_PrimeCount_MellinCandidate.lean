import HVR_Zeta_CorrectionIdentity
import HVR_PrimeMellin_ModeAssembly

noncomputable section
open scoped BigOperators
open Filter Asymptotics
open HVRPrimeZetaSplit HVRZetaLogDerivative
open HVRPowerCorrectionHolomorphic HVRZetaCorrectionIdentity

/-!
Direct prime-mode candidate for the prime-count Mellin bridge. The original
public theorem signatures, including hr, hrs and hO, are preserved exactly;
the new proof establishes the identity using only sigma > 1 and does not
require those extra arguments.
The mode-series interchange still uses Mathlib integral_tsum, and all
transitive dependency/axiom claims require separate external audit.
This refactored source has not yet been compiled.
-/
namespace HVRPrimeCountMellin

/-- Partial summation for the actual prime series, conditional on its stated
elementary partial-sum growth bound. -/
theorem primeSeries_eq_mul_primeThetaMellin (sigma t r : ℝ)
    (hsigma : 1 < sigma) (hr : 0 ≤ r) (hrs : r < sigma)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoefficientC k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    HVRPrimeComplex.primeSeries sigma t 1 =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) := by
  exact HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes sigma t hsigma

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
