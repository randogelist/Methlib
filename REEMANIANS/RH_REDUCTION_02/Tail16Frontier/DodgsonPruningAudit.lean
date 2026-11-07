import Tail16Frontier.DodgsonPruning

/-! External compiler/audit targets. No claimed compiler result is embedded. -/

set_option autoImplicit false

example
    (project : (Nat × Tail16Admission.Proof) → List RHFinitePruning.Dodgson.Cell)
    (Y : Nat) (p : Tail16Admission.Proof)
    (h : Tail16Frontier.checkBudgetPruned project Y p = true) :
    _root_.RiemannHypothesis := by
  exact Tail16Frontier.checkBudgetPruned_sound project Y p h

example
    (F : RHFrozenWitness.TailKernel.CertifiedDodgsonProjection
      Tail16Frontier.fixedPrimitiveKernel)
    (Y : Nat) (p : Tail16Admission.Proof) :
    Tail16Frontier.checkBudgetPruned F.cells Y p =
      Tail16Frontier.checkBudget Y p := by
  exact Tail16Frontier.checkBudgetPruned_eq_original F Y p

example (K : RHFrozenWitness.TailKernel)
    (F : RHFrozenWitness.TailKernel.CertifiedDodgsonProjection K) :
    (∃ c : K.Cert, RHFrozenWitness.TailKernel.checkPruned K F.cells c = true) ↔
      ∃ c : K.Cert, K.check c = true := by
  exact RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.exists_accepted_iff K F

#check RHFinitePruning.checkPruned_accepts_keep
#print axioms RHFinitePruning.checkPruned_accepts_keep

#check RHFinitePruning.checkPruned_accepts_check
#print axioms RHFinitePruning.checkPruned_accepts_check

#check RHFinitePruning.checkPruned_sound
#print axioms RHFinitePruning.checkPruned_sound

#check RHFinitePruning.checkPruned_sound_at
#print axioms RHFinitePruning.checkPruned_sound_at

#check RHFinitePruning.checkPruned_eq_check
#print axioms RHFinitePruning.checkPruned_eq_check

#check RHFinitePruning.checkPruned_eq
#print axioms RHFinitePruning.checkPruned_eq

#check RHFinitePruning.checkPruned_accept_iff
#print axioms RHFinitePruning.checkPruned_accept_iff

#check RHFinitePruning.checkPruned_exists_iff
#print axioms RHFinitePruning.checkPruned_exists_iff

#check RHFinitePruning.checkPruned_false_of_keep_false
#print axioms RHFinitePruning.checkPruned_false_of_keep_false

#check RHFinitePruning.check_false_of_keep_false
#print axioms RHFinitePruning.check_false_of_keep_false

#check RHFinitePruning.Dodgson.Cell.valid_turan_pos
#print axioms RHFinitePruning.Dodgson.Cell.valid_turan_pos

#check RHFinitePruning.Dodgson.Cell.valid_necessaryTest
#print axioms RHFinitePruning.Dodgson.Cell.valid_necessaryTest

#check RHFinitePruning.Dodgson.Cell.valid_recurrenceTest
#print axioms RHFinitePruning.Dodgson.Cell.valid_recurrenceTest

#check RHFinitePruning.Dodgson.Cell.necessaryTest_false_not_valid
#print axioms RHFinitePruning.Dodgson.Cell.necessaryTest_false_not_valid

#check RHFinitePruning.Dodgson.Cell.recurrenceTest_false_not_valid
#print axioms RHFinitePruning.Dodgson.Cell.recurrenceTest_false_not_valid

#check RHFinitePruning.Dodgson.Cell.not_valid_of_turan_nonpos
#print axioms RHFinitePruning.Dodgson.Cell.not_valid_of_turan_nonpos

#check RHFinitePruning.Dodgson.allValid_necessaryDodgsonTests
#print axioms RHFinitePruning.Dodgson.allValid_necessaryDodgsonTests

#check RHFinitePruning.Dodgson.necessaryDodgsonTests_false_not_allValid
#print axioms RHFinitePruning.Dodgson.necessaryDodgsonTests_false_not_allValid

#check RHFinitePruning.Dodgson.geometricCell_turan
#print axioms RHFinitePruning.Dodgson.geometricCell_turan

#check RHFinitePruning.Dodgson.geometricCell_rejected
#print axioms RHFinitePruning.Dodgson.geometricCell_rejected

#check RHFinitePruning.Dodgson.geometricCell_not_valid
#print axioms RHFinitePruning.Dodgson.geometricCell_not_valid

#check RHFinitePruning.Dodgson.family_excluded_of_upper_bound
#print axioms RHFinitePruning.Dodgson.family_excluded_of_upper_bound

#check RHFinitePruning.Dodgson.positiveControl_valid
#print axioms RHFinitePruning.Dodgson.positiveControl_valid

#check RHFinitePruning.Dodgson.positiveControl_accepted
#print axioms RHFinitePruning.Dodgson.positiveControl_accepted

#check RHFinitePruning.Dodgson.negativeControl_rejected
#print axioms RHFinitePruning.Dodgson.negativeControl_rejected

#check RHFinitePruning.Dodgson.mixedControls_rejected
#print axioms RHFinitePruning.Dodgson.mixedControls_rejected

#check RHFrozenWitness.TailKernel.checkPruned_implies_original
#print axioms RHFrozenWitness.TailKernel.checkPruned_implies_original

#check RHFrozenWitness.TailKernel.checkPruned_sound
#print axioms RHFrozenWitness.TailKernel.checkPruned_sound

#check RHFrozenWitness.TailKernel.verifyPruned_sound
#print axioms RHFrozenWitness.TailKernel.verifyPruned_sound

#check RHFrozenWitness.TailKernel.verifyPruned_eq_original
#print axioms RHFrozenWitness.TailKernel.verifyPruned_eq_original

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.necessary
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.necessary

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.checkPruned_eq_original
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.checkPruned_eq_original

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.acceptance_iff
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.acceptance_iff

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.exists_accepted_iff
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.exists_accepted_iff

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.original_rejected_of_crossout
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.original_rejected_of_crossout

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.family_rejected_of_crossout
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.family_rejected_of_crossout

#check RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.empty_check_eq_original
#print axioms RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.empty_check_eq_original

#check Tail16Frontier.checkBudgetPruned_sound
#print axioms Tail16Frontier.checkBudgetPruned_sound

#check Tail16Frontier.checkBudgetPruned_eq_original
#print axioms Tail16Frontier.checkBudgetPruned_eq_original

#check Tail16Frontier.checkBudgetPruned_truth_rejected
#print axioms Tail16Frontier.checkBudgetPruned_truth_rejected
