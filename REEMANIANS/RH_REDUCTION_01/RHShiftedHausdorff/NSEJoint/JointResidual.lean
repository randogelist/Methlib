import RHShiftedHausdorff.NSEJoint.NSEReference

set_option autoImplicit false
noncomputable section

namespace RHShiftedHausdorff.NSEJoint

open RH_HilbertLimit.TwoRoutes

def nseResidual (M : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  actualShiftedMoment4 n - α * nseReference M n

theorem shifted_eq_residual_add_reference
    (M : ℕ) (α : ℝ) :
    actualShiftedMoment4 =
      (fun n => nseResidual M α n + α * nseReference M n) := by
  funext n
  simp [nseResidual]

theorem actual_shifted_bernsteinPositive_of_nse_residual_positive
    (M : ℕ) (α : ℝ)
    (hα : 0 ≤ α)
    (hres : BernsteinPositive (nseResidual M α)) :
    BernsteinPositive actualShiftedMoment4 := by
  have href : BernsteinPositive (fun n => α * nseReference M n) :=
    bernsteinPositive_smul hα (nseReference_bernsteinPositive M)
  have hadd :
      BernsteinPositive
        (fun n => nseResidual M α n + α * nseReference M n) :=
    bernsteinPositive_add hres href
  rw [shifted_eq_residual_add_reference M α]
  exact hadd

end RHShiftedHausdorff.NSEJoint
