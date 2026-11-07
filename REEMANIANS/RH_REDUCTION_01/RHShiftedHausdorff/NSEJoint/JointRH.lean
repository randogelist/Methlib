import RHShiftedHausdorff.NSEJoint.JointResidual

set_option autoImplicit false
noncomputable section

namespace RHShiftedHausdorff.NSEJoint

open RH_HilbertLimit.TwoRoutes

theorem nativeRH_of_nse_residual_positive
    (M : ℕ) (α : ℝ)
    (hα : 0 ≤ α)
    (hres : BernsteinPositive (nseResidual M α)) :
    _root_.RiemannHypothesis := by
  exact actual_shifted_bernsteinPositive_implies_nativeRH
    (actual_shifted_bernsteinPositive_of_nse_residual_positive
      M α hα hres)

theorem nativeRH_of_exists_nse_residual_positive
    (h :
      ∃ M : ℕ, ∃ α : ℝ,
        0 < α ∧ BernsteinPositive (nseResidual M α)) :
    _root_.RiemannHypothesis := by
  obtain ⟨M, α, hα, hres⟩ := h
  exact nativeRH_of_nse_residual_positive M α hα.le hres

end RHShiftedHausdorff.NSEJoint
