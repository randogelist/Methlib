import HVR_PrimeCount_MellinGerm
import HVR_PrimeCount_MellinConversion
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open MeasureTheory
open HVRPrimeCountMellin HVRPrimeCountMellinGerm HVRPrimeZetaSplit
open HVRSmoothingAnalyticGerms

/-!
Candidate change of variables for the actual prime-count Mellin integral.
Bochner integrals are used throughout; this module does not itself assert
integrability, the pole-subtracted Laplace integral, or the Fourier limits.
No local Lean run was performed. -/
namespace HVRPrimeCountLogSubstitution

/-- The unregularized exponential integral has the same pole-subtracted
expression as the previously certified analytic germ. -/
theorem exp_integral_sub_pole_eq_regularPartAt
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    (∫ u : ℝ in Set.Ioi 0,
      primeTheta (Real.exp u) * Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) -
        (zetaPoint sigma t - 1)⁻¹ = regularPartAt (zetaPoint sigma t) := by
  rw [← primeThetaMellin_eq_exp_integral]
  exact primeThetaMellin_sub_pole_eq_regularPartAt_of_growth sigma t hsigma

end HVRPrimeCountLogSubstitution
