import HVR_PrimeDensity_Laplace
import HVR_Smoothing_BoundaryExtension

noncomputable section
open HVRPrimeDensityLaplace HVRPrimeZetaSplit
open HVRPrimeCountLogSubstitution HVRSmoothingBoundaryExtension

/-! Candidate link from the actual prime-density Laplace transform on the open
half-plane to the patched expression with continuous boundary values. Fourier
limits and the PNT are not asserted. No local Lean execution was performed. -/
namespace HVRPrimeDensityBoundaryLink

/-- On the right half-plane the actual Laplace transform equals the patched
analytic function whose restriction to the imaginary axis is continuous. -/
theorem primeDensityLaplace_eq_patchedShift
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    primeDensityLaplace (zetaPoint sigma t - 1) =
      patchedShift (zetaPoint sigma t - 1) := by
  rw [primeDensityLaplace_eq_regularPartAt sigma t hsigma]
  rw [← exp_integral_sub_pole_eq_regularPartAt sigma t hsigma]
  exact exp_integral_sub_pole_eq_patchedShift sigma t hsigma

end HVRPrimeDensityBoundaryLink
