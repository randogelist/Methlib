import Tail16Frontier.LogicalFrontier
import Tail16Frontier.CheckedAdmission

/-!
Exact scope:
  rational finite checks + native actual-moment proofs -> finite admission;
  an additional native universal-tail proof -> literal Mathlib RH.
No general raw theta-source checker or accepted RH witness is supplied.
-/
set_option autoImplicit false

namespace Tail16Frontier

/-- A complete native proof-carrying witness, including the universal proof. -/
structure CompleteAdmission where
  finite : CheckedSignAdmission
  tail : Tail finite.coefficient finite.cutoff

theorem CompleteAdmission.nativeRH (w : CompleteAdmission) :
    _root_.RiemannHypothesis :=
  w.finite.nativeRH w.tail

theorem nativeRH_of_completeAdmission_exists
    (h : Nonempty CompleteAdmission) : _root_.RiemannHypothesis := by
  rcases h with ⟨w⟩
  exact w.nativeRH

/-- Genuine actual-xi sign control at maximum row one; no RH assumption. -/
def firstRowAdmission : CheckedSignAdmission :=
  { coefficient := 1
    cutoff := 1
    data := firstMomentData
    actualBounds := firstMomentData_encloses
    accepted := firstMomentData_signCheck }

theorem firstRowCancellation :
    RH_HilbertLimit.rowCancellation
      RH_HilbertLimit.actualNormalizedMoment 0 = 0 := by
  exact cancellation_eq_zero_of_nonnegative_row 1
    firstMomentData_row_nonnegative 0 (by decide)

/-- The finite control is not asserted to provide any universal tail. -/
theorem firstRowFinitePrefix : Prefix 1 1 :=
  firstRowAdmission.prefix

end Tail16Frontier

