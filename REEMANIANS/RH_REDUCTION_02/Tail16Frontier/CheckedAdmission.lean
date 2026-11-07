import Tail16Frontier.NumericalChecks
import Tail16Frontier.BoolFacts

/-!
# Finite numerical prefix admission with explicit actual-moment evidence

All numerical checks below are executable rational checks. Their semantic
soundness consumes native proofs of the actual moment enclosures. Such
proofs are not inferred from the Boolean arithmetic result.

A universal tail proof is an additional native input for the RH endpoint.
-/

set_option autoImplicit false

namespace Tail16Frontier

/-- Native actual-moment evidence for the finite list of successive steps. -/
def PrefixRowsEnclose : Nat → List MomentData → Prop
  | _, [] => True
  | n, d :: ds => d.Encloses (n + 1) ∧ PrefixRowsEnclose (n + 1) ds

/-- Executable rational checks for a finite list of successive steps. -/
def checkPrefixRows (Y : Nat) : Nat → List MomentData → Bool
  | _, [] => true
  | n, d :: ds => marginCheck d n Y && checkPrefixRows Y (n + 1) ds

theorem checkPrefixRows_sound (Y : Nat) (rows : List MomentData) :
    ∀ n : Nat,
      PrefixRowsEnclose n rows →
      checkPrefixRows Y n rows = true →
      ∀ i : Nat, i < rows.length → BudgetStep Y (n + i) := by
  induction rows with
  | nil =>
      intro n _hData _hCheck i hi
      simp at hi
  | cons d ds ih =>
      intro n hData hCheck i hi
      change d.Encloses (n + 1) ∧ PrefixRowsEnclose (n + 1) ds at hData
      change (marginCheck d n Y && checkPrefixRows Y (n + 1) ds) = true at hCheck
      rcases hData with ⟨hd, hds⟩
      rcases Tail16Bool.andTrue hCheck with ⟨hc, hcs⟩
      cases i with
      | zero =>
          simpa only [Nat.add_zero] using marginCheck_sound d n Y hd hc
      | succ i =>
          have hi' : i < ds.length := by
            simp only [List.length_cons] at hi
            omega
          have hs := ih (n + 1) hds hcs i hi'
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
            Nat.add_comm 1 i] using hs

/--
Finite rational prefix data. The list contains one MomentData object per
step, so each margin check can enforce its own exact degree/shape.
-/
structure PrefixData where
  coefficient : Nat
  cutoff : Nat
  rows : List MomentData

def PrefixData.check (d : PrefixData) : Bool :=
  decide (16 ≤ d.cutoff ∧ d.rows.length = d.cutoff - 16) &&
    checkPrefixRows d.coefficient 16 d.rows

def PrefixData.Encloses (d : PrefixData) : Prop :=
  PrefixRowsEnclose 16 d.rows

theorem prefixData_check_sound
    (d : PrefixData) (hData : d.Encloses) (hCheck : d.check = true) :
    Prefix d.coefficient d.cutoff := by
  change
    (decide (16 ≤ d.cutoff ∧ d.rows.length = d.cutoff - 16) &&
      checkPrefixRows d.coefficient 16 d.rows) = true at hCheck
  rcases Tail16Bool.andTrue hCheck with ⟨hShape, hRows⟩
  have hShape' : 16 ≤ d.cutoff ∧ d.rows.length = d.cutoff - 16 :=
    of_decide_eq_true hShape
  rcases hShape' with ⟨hCutoff, hLength⟩
  intro n hn hlt
  have hi : n - 16 < d.rows.length := by
    omega
  have hIndex : 16 + (n - 16) = n := by
    omega
  have hs := checkPrefixRows_sound
    d.coefficient d.rows 16 hData hRows (n - 16) hi
  simpa only [hIndex] using hs

/-- One maximum-row sign check gives the entire finite prefix. -/
theorem signCheck_prefix
    (d : MomentData) (Y M : Nat)
    (hData : d.Encloses M) (hCheck : signCheck d M = true) :
    Prefix Y M := by
  exact prefix_of_nonnegative_row Y M (signCheck_sound d M hData hCheck)

theorem prefixData_check_nativeRH
    (d : PrefixData) (hData : d.Encloses) (hCheck : d.check = true)
    (hTail : Tail d.coefficient d.cutoff) :
    _root_.RiemannHypothesis := by
  exact prefix_tail_nativeRH d.coefficient d.cutoff
    (prefixData_check_sound d hData hCheck) hTail

theorem signCheck_nativeRH
    (d : MomentData) (Y M : Nat)
    (hData : d.Encloses M) (hCheck : signCheck d M = true)
    (hTail : Tail Y M) :
    _root_.RiemannHypothesis := by
  exact prefix_tail_nativeRH Y M (signCheck_prefix d Y M hData hCheck) hTail

/--
Typed native admission output. The actualBounds field must be a checked
proof; Boolean acceptance alone is insufficient for actual semantics.
-/
structure CheckedPrefixAdmission where
  data : PrefixData
  actualBounds : data.Encloses
  accepted : data.check = true

theorem CheckedPrefixAdmission.prefix (w : CheckedPrefixAdmission) :
    Prefix w.data.coefficient w.data.cutoff := by
  exact prefixData_check_sound w.data w.actualBounds w.accepted

theorem CheckedPrefixAdmission.nativeRH
    (w : CheckedPrefixAdmission)
    (hTail : Tail w.data.coefficient w.data.cutoff) :
    _root_.RiemannHypothesis := by
  exact prefixData_check_nativeRH w.data w.actualBounds w.accepted hTail

/-- Typed native admission output for the single-row method. -/
structure CheckedSignAdmission where
  coefficient : Nat
  cutoff : Nat
  data : MomentData
  actualBounds : data.Encloses cutoff
  accepted : signCheck data cutoff = true

theorem CheckedSignAdmission.prefix (w : CheckedSignAdmission) :
    Prefix w.coefficient w.cutoff := by
  exact signCheck_prefix
    w.data w.coefficient w.cutoff w.actualBounds w.accepted

theorem CheckedSignAdmission.nativeRH
    (w : CheckedSignAdmission)
    (hTail : Tail w.coefficient w.cutoff) :
    _root_.RiemannHypothesis := by
  exact signCheck_nativeRH
    w.data w.coefficient w.cutoff w.actualBounds w.accepted hTail

/-- Empty-prefix data are an honest finite control with no tail claim. -/
def emptyPrefixData (Y : Nat) : PrefixData :=
  { coefficient := Y, cutoff := 16, rows := [] }

theorem emptyPrefixData_check (Y : Nat) :
    (emptyPrefixData Y).check = true := by
  rfl

theorem emptyPrefixData_encloses (Y : Nat) :
    (emptyPrefixData Y).Encloses := by
  trivial

theorem emptyPrefixData_valid (Y : Nat) :
    Prefix Y 16 := by
  exact prefixData_check_sound
    (emptyPrefixData Y) (emptyPrefixData_encloses Y) (emptyPrefixData_check Y)

end Tail16Frontier

