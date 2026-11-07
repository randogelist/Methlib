import Tail16Admission.Soundness

set_option autoImplicit false

namespace Tail16Frontier

open Tail16Admission

/-- The final target is fixed by the decoded coefficient. -/
def checkBudget (Y : Nat) (p : Proof) : Bool :=
  checkProof 0 [] p (budgetFormula Y)

theorem checkBudget_admissible {Y : Nat} {p : Proof}
    (h : checkBudget Y p = true) :
    (RHFrozenWitness.budget16 Y).Admissible := by
  exact (budgetFormula_iff_admissible Y).1 (checkProof_sound h)

theorem checkBudget_sound {Y : Nat} {p : Proof}
    (h : checkBudget Y p = true) : _root_.RiemannHypothesis := by
  exact RH_HilbertLimit.nativeRH_of_admissible_cancellationBudget
    (RHFrozenWitness.budget16 Y) (checkBudget_admissible h)

/-- A concrete sound interface; no accepted universal-budget witness is claimed. -/
def fixedPrimitiveKernel : RHFrozenWitness.TailKernel where
  Cert := Nat × Proof
  coefficient c := c.1
  check c := checkBudget c.1 c.2
  sound c h := checkBudget_admissible h

def cancellationIdentityProof (n : Nat) : Proof :=
  .prim (.cancellationIdentity (.lit n))

def cancellationNonnegativeProof (n : Nat) : Proof :=
  .prim (.cancellationNonnegative (.lit n))

theorem cancellationIdentityProof_check (n : Nat) :
    checkProof 0 [] (cancellationIdentityProof n)
      (ActualPrimitive.cancellationIdentity (.lit n)).conclusion = true := by
  simp [checkProof, infer, cancellationIdentityProof,
    ActualPrimitive.check, ActualPrimitive.wellScoped, NExpr.wellScoped]

theorem cancellationNonnegativeProof_check (n : Nat) :
    checkProof 0 [] (cancellationNonnegativeProof n)
      (ActualPrimitive.cancellationNonnegative (.lit n)).conclusion = true := by
  simp [checkProof, infer, cancellationNonnegativeProof,
    ActualPrimitive.check, ActualPrimitive.wellScoped, NExpr.wellScoped]

def allCancellationNonnegative : Formula :=
  .all (ActualPrimitive.cancellationNonnegative (.var 0)).conclusion

def allCancellationNonnegativeProof : Proof :=
  .allI (.prim (.cancellationNonnegative (.var 0)))

theorem allCancellationNonnegative_check :
    checkProof 0 [] allCancellationNonnegativeProof
      allCancellationNonnegative = true := by
  rfl

theorem allCancellationNonnegative_valid :
    Holds [] allCancellationNonnegative :=
  checkProof_sound allCancellationNonnegative_check

def inductionTruthProof : Proof :=
  .natInd .top .triv .triv

theorem inductionTruth_check :
    checkProof 0 [] inductionTruthProof (.all .top) = true := by
  rfl

theorem inductionTruth_valid : Holds [] (.all .top) :=
  checkProof_sound inductionTruth_check

theorem unboundPrimitive_rejected :
    checkProof 0 [] (.prim (.cancellationNonnegative (.var 0)))
      (ActualPrimitive.cancellationNonnegative (.var 0)).conclusion = false := by
  rfl

theorem truth_is_not_budget : checkBudget 0 .triv = false := by
  rfl

/-- Closed actual numeric primitive, with no coordinate or proof payload. -/
def momentZeroProof : Proof := .prim .momentZero

theorem momentZeroProof_check :
    checkProof 0 [] momentZeroProof ActualPrimitive.momentZero.conclusion = true := by
  decide

theorem momentZeroProof_valid : Holds [] ActualPrimitive.momentZero.conclusion :=
  checkProof_sound momentZeroProof_check

theorem momentZeroProof_actual : RH_HilbertLimit.actualNormalizedMoment 0 = 1 := by
  simpa [ActualPrimitive.conclusion, Holds, denoteR, denoteN] using
    momentZeroProof_valid

/-- Both first-moment inequalities are independently fixed actual primitives. -/
def momentOneBounds : Formula :=
  .conj ActualPrimitive.momentOneLower.conclusion
    ActualPrimitive.momentOneUpper.conclusion

def momentOneBoundsProof : Proof :=
  .andI (.prim .momentOneLower) (.prim .momentOneUpper)

theorem momentOneBounds_check :
    checkProof 0 [] momentOneBoundsProof momentOneBounds = true := by
  decide

theorem momentOneBounds_valid : Holds [] momentOneBounds :=
  checkProof_sound momentOneBounds_check

theorem momentOneBounds_actual :
    0 ≤ RH_HilbertLimit.actualNormalizedMoment 1 ∧
    RH_HilbertLimit.actualNormalizedMoment 1 ≤ 1 := by
  simpa [momentOneBounds, ActualPrimitive.conclusion, Holds, denoteR, denoteN] using
    momentOneBounds_valid

end Tail16Frontier
