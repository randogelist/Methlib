import HVR_HigherCoefficient_Geometric
import HVR_Correction_PrimeSubtype

noncomputable section

/-!
Candidate identity connecting the actual higher coefficient L-series to the
geometrically resummed complex correction. No boundary nonvanishing or PNT
is claimed. This file requires an external compiler and axiom audit.
-/
namespace HVRZetaCorrectionIdentity

open HVRPrimeZetaSplit HVRPowerCorrectionHolomorphic
open HVRHigherCoefficientReindex HVRHigherCoefficientGeometric
open HVRCorrectionPrimeSubtype

theorem higher_lseries_eq_complexCorrection (sigma t : ℝ) (hsigma : 1 < sigma) :
    LSeries higherCoefficientC (zetaPoint sigma t) =
      complexCorrection (zetaPoint sigma t) := by
  rw [higher_lseries_eq_prime_power_tsum sigma t hsigma,
    complexCorrection_eq_prime_tsum]
  apply tsum_congr
  intro p
  exact correction_prime_power_tsum p.property sigma t hsigma

theorem zeta_log_deriv_eq_primeSeries_add_complexCorrection
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    -deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) =
      HVRPrimeComplex.primeSeries sigma t 1 + complexCorrection (zetaPoint sigma t) := by
  rw [← higher_lseries_eq_complexCorrection sigma t hsigma]
  exact zeta_log_deriv_eq_primeSeries_add_higher sigma t hsigma

end HVRZetaCorrectionIdentity
