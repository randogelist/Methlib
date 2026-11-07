import RHFinitePruning.PruningCore
import RHFinitePruning.DodgsonCells
import Tail16Frontier.LogicalFrontier

/-!
Finite Dodgson tests precede the unchanged frozen RH checker.
RH soundness holds for every projection. Preservation of every accepted
certificate requires a proof that the projected cells are valid on acceptance.
No actual-xi determinant projection is postulated by this module.
-/

set_option autoImplicit false

namespace RHFrozenWitness.TailKernel

abbrev DodgsonProjection (K : TailKernel) :=
  K.Cert → List RHFinitePruning.Dodgson.Cell

def necessaryDodgsonTests (K : TailKernel)
    (project : DodgsonProjection K) (c : K.Cert) : Bool :=
  RHFinitePruning.Dodgson.necessaryDodgsonTests (project c)

def checkPruned (K : TailKernel)
    (project : DodgsonProjection K) (c : K.Cert) : Bool :=
  RHFinitePruning.checkPruned (necessaryDodgsonTests K project) K.check c

theorem checkPruned_implies_original (K : TailKernel)
    (project : DodgsonProjection K) (c : K.Cert)
    (h : checkPruned K project c = true) : K.check c = true := by
  exact RHFinitePruning.checkPruned_accepts_check
    (necessaryDodgsonTests K project) K.check c h

theorem checkPruned_sound (K : TailKernel)
    (project : DodgsonProjection K) (c : K.Cert)
    (h : checkPruned K project c = true) : _root_.RiemannHypothesis := by
  exact K.check_sound c (checkPruned_implies_original K project c h)

/-- An adapter to the same root interface; no extra RH premise is added. -/
def prunedKernel (K : TailKernel) (project : DodgsonProjection K) : TailKernel where
  Cert := K.Cert
  coefficient := K.coefficient
  check := checkPruned K project
  sound c h := K.sound c (checkPruned_implies_original K project c h)

/-- This fixed projection proof is needed only for accepted-set preservation. -/
structure CertifiedDodgsonProjection (K : TailKernel) where
  cells : DodgsonProjection K
  valid_of_accepted : ∀ c : K.Cert, K.check c = true →
    RHFinitePruning.Dodgson.AllValid (cells c)

namespace CertifiedDodgsonProjection

theorem necessary (K : TailKernel) (F : CertifiedDodgsonProjection K)
    (c : K.Cert) (h : K.check c = true) :
    necessaryDodgsonTests K F.cells c = true := by
  exact RHFinitePruning.Dodgson.allValid_necessaryDodgsonTests
    (F.cells c) (F.valid_of_accepted c h)

theorem checkPruned_eq_original (K : TailKernel)
    (F : CertifiedDodgsonProjection K) (c : K.Cert) :
    checkPruned K F.cells c = K.check c := by
  exact RHFinitePruning.checkPruned_eq_check
    (necessaryDodgsonTests K F.cells) K.check (necessary K F) c

theorem acceptance_iff (K : TailKernel)
    (F : CertifiedDodgsonProjection K) (c : K.Cert) :
    checkPruned K F.cells c = true ↔ K.check c = true := by
  rw [checkPruned_eq_original K F c]

theorem exists_accepted_iff (K : TailKernel)
    (F : CertifiedDodgsonProjection K) :
    (∃ c : K.Cert, checkPruned K F.cells c = true) ↔
      ∃ c : K.Cert, K.check c = true := by
  exact RHFinitePruning.checkPruned_exists_iff
    (necessaryDodgsonTests K F.cells) K.check (necessary K F)

theorem original_rejected_of_crossout (K : TailKernel)
    (F : CertifiedDodgsonProjection K) (c : K.Cert)
    (h : necessaryDodgsonTests K F.cells c = false) : K.check c = false := by
  exact RHFinitePruning.check_false_of_keep_false
    (necessaryDodgsonTests K F.cells) K.check (necessary K F) c h

theorem family_rejected_of_crossout {α : Type*} (K : TailKernel)
    (F : CertifiedDodgsonProjection K) (family : α → K.Cert)
    (region : α → Prop)
    (h : ∀ θ, region θ →
      necessaryDodgsonTests K F.cells (family θ) = false) :
    ∀ θ, region θ → K.check (family θ) = false := by
  intro θ hθ
  exact original_rejected_of_crossout K F (family θ) (h θ hθ)

/-- Concrete identity control. It supplies no numerical search reduction. -/
def empty (K : TailKernel) : CertifiedDodgsonProjection K where
  cells := fun _ => []
  valid_of_accepted := by
    intro c h
    trivial

theorem empty_check_eq_original (K : TailKernel) (c : K.Cert) :
    checkPruned K (empty K).cells c = K.check c := by
  exact checkPruned_eq_original K (empty K) c

end CertifiedDodgsonProjection

def verifyPruned (K : TailKernel) (project : DodgsonProjection K)
    (D : Decoder K) (blob : ByteArray) : Bool :=
  match D.decode blob with
  | none => false
  | some c => checkPruned K project c

theorem verifyPruned_sound (K : TailKernel) (project : DodgsonProjection K)
    (D : Decoder K) (blob : ByteArray)
    (h : verifyPruned K project D blob = true) : _root_.RiemannHypothesis := by
  unfold verifyPruned at h
  cases hdec : D.decode blob with
  | none => simp [hdec] at h
  | some c =>
      have hc : checkPruned K project c = true := by
        simpa [hdec] using h
      exact checkPruned_sound K project c hc

theorem verifyPruned_eq_original (K : TailKernel)
    (F : CertifiedDodgsonProjection K) (D : Decoder K) (blob : ByteArray) :
    verifyPruned K F.cells D blob = verify K D blob := by
  unfold verifyPruned verify
  cases hdec : D.decode blob with
  | none => rfl
  | some c => exact CertifiedDodgsonProjection.checkPruned_eq_original K F c

end RHFrozenWitness.TailKernel

namespace Tail16Frontier

/-- Direct connection to the existing FIX6 finite proof checker. -/
def checkBudgetPruned
    (project : (Nat × Tail16Admission.Proof) → List RHFinitePruning.Dodgson.Cell)
    (Y : Nat) (p : Tail16Admission.Proof) : Bool :=
  RHFrozenWitness.TailKernel.checkPruned fixedPrimitiveKernel project (Y, p)

theorem checkBudgetPruned_sound
    (project : (Nat × Tail16Admission.Proof) → List RHFinitePruning.Dodgson.Cell)
    (Y : Nat) (p : Tail16Admission.Proof)
    (h : checkBudgetPruned project Y p = true) : _root_.RiemannHypothesis := by
  exact RHFrozenWitness.TailKernel.checkPruned_sound
    fixedPrimitiveKernel project (Y, p) h

theorem checkBudgetPruned_eq_original
    (F : RHFrozenWitness.TailKernel.CertifiedDodgsonProjection fixedPrimitiveKernel)
    (Y : Nat) (p : Tail16Admission.Proof) :
    checkBudgetPruned F.cells Y p = checkBudget Y p := by
  exact RHFrozenWitness.TailKernel.CertifiedDodgsonProjection.checkPruned_eq_original
    fixedPrimitiveKernel F (Y, p)

theorem checkBudgetPruned_truth_rejected
    (project : (Nat × Tail16Admission.Proof) → List RHFinitePruning.Dodgson.Cell) :
    checkBudgetPruned project 0 .triv = false := by
  change (RHFinitePruning.Dodgson.necessaryDodgsonTests (project (0, .triv)) &&
    checkBudget 0 .triv) = false
  rw [truth_is_not_budget]
  cases RHFinitePruning.Dodgson.necessaryDodgsonTests (project (0, .triv)) <;> rfl

end Tail16Frontier
