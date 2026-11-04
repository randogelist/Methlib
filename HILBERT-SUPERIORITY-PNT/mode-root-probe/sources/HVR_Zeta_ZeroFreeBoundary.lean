import HVR_Zeta_GramResidueConditional
import HVR_Zeta_BoundarySequence

noncomputable section

/-!
Candidate actual zeta zero-free boundary using the prime Gram contradiction.
The proof and exact dependencies require the external build and named axiom
audit; independence from existing PNT and boundary-nonvanishing theorems
requires a separate proof-dependency inspection.
-/
namespace HVRZetaZeroFreeBoundary

open HVRCorrectionBoundaryLimit HVRZetaBoundarySequence
open HVRZetaGramResidueConditional

/-- The actual zeta function has no zeros at 1 + it for t ≠ 0. -/
theorem zeta_nonzero_on_one_line :
    ∀ t : ℝ, t ≠ 0 → riemannZeta (boundaryPoint t) ≠ 0 := by
  apply nonvanishing_of_all_zeta_residues
  intro t ht
  simpa only [ZetaBoundaryResidueLimit, boundaryZetaOrder] using
    zeta_boundary_neg_logderiv_sequence t ht

end HVRZetaZeroFreeBoundary
