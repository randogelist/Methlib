import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Finite necessary tests for a strictly positive Dodgson cell.

`Valid` includes the recurrence and the two strictly positive determinant
factors. Actual-source calibration and the accepted-witness-to-`Valid`
bridge belong to the importing admission module.
-/

set_option autoImplicit false

namespace RHFinitePruning.Dodgson

structure Cell where
  leftEntry : ℚ
  middleEntry : ℚ
  rightEntry : ℚ
  nextDet : ℚ
  pivot : ℚ
deriving Repr, DecidableEq

namespace Cell

def turan (c : Cell) : ℚ :=
  c.leftEntry * c.rightEntry - c.middleEntry ^ 2

def Valid (c : Cell) : Prop :=
  c.nextDet * c.pivot = c.turan ∧
    0 < c.nextDet ∧ 0 < c.pivot

/-- A necessary positivity test; acceptance is not full admission. -/
def necessaryTest (c : Cell) : Bool :=
  decide (0 < c.turan)

/-- Exact finite recurrence consistency for the supplied rational cell. -/
def recurrenceTest (c : Cell) : Bool :=
  decide (c.nextDet * c.pivot = c.turan)

theorem valid_turan_pos (c : Cell) (h : c.Valid) :
    0 < c.turan := by
  rcases h with ⟨hrec, hnext, hpivot⟩
  rw [← hrec]
  exact mul_pos hnext hpivot

theorem valid_necessaryTest (c : Cell) (h : c.Valid) :
    c.necessaryTest = true := by
  simp [necessaryTest, valid_turan_pos c h]

theorem valid_recurrenceTest (c : Cell) (h : c.Valid) :
    c.recurrenceTest = true := by
  simp [recurrenceTest, h.1]

theorem necessaryTest_false_not_valid (c : Cell)
    (hfalse : c.necessaryTest = false) : ¬ c.Valid := by
  intro h
  have htrue := valid_necessaryTest c h
  rw [htrue] at hfalse
  cases hfalse

theorem recurrenceTest_false_not_valid (c : Cell)
    (hfalse : c.recurrenceTest = false) : ¬ c.Valid := by
  intro h
  have htrue := valid_recurrenceTest c h
  rw [htrue] at hfalse
  cases hfalse

theorem not_valid_of_turan_nonpos (c : Cell)
    (hupper : c.turan ≤ 0) : ¬ c.Valid := by
  intro h
  exact (not_lt_of_ge hupper) (valid_turan_pos c h)

end Cell

def AllValid : List Cell → Prop
  | [] => True
  | c :: cs => c.Valid ∧ AllValid cs

def necessaryDodgsonTests : List Cell → Bool
  | [] => true
  | c :: cs => c.necessaryTest && necessaryDodgsonTests cs

theorem allValid_necessaryDodgsonTests (cells : List Cell) :
    AllValid cells → necessaryDodgsonTests cells = true := by
  induction cells with
  | nil =>
      intro _
      rfl
  | cons c cs ih =>
      intro h
      rcases h with ⟨hc, hcs⟩
      simp [necessaryDodgsonTests, Cell.valid_necessaryTest c hc, ih hcs]

theorem necessaryDodgsonTests_false_not_allValid (cells : List Cell)
    (hfalse : necessaryDodgsonTests cells = false) : ¬ AllValid cells := by
  intro h
  have htrue := allValid_necessaryDodgsonTests cells h
  rw [htrue] at hfalse
  cases hfalse

/-- A geometric triple in the shift coordinate has zero Turan numerator. -/
def geometricCell (a q nextDet pivot : ℚ) : Cell where
  leftEntry := a
  middleEntry := a * q
  rightEntry := a * q ^ 2
  nextDet := nextDet
  pivot := pivot

@[simp] theorem geometricCell_turan (a q nextDet pivot : ℚ) :
    (geometricCell a q nextDet pivot).turan = 0 := by
  unfold geometricCell Cell.turan
  ring

theorem geometricCell_rejected (a q nextDet pivot : ℚ) :
    (geometricCell a q nextDet pivot).necessaryTest = false := by
  simp [Cell.necessaryTest]

theorem geometricCell_not_valid (a q nextDet pivot : ℚ) :
    ¬ (geometricCell a q nextDet pivot).Valid := by
  exact Cell.necessaryTest_false_not_valid _
    (geometricCell_rejected a q nextDet pivot)

/-- A uniform upper bound excludes an entire represented parameter family. -/
theorem family_excluded_of_upper_bound
    {α : Type*} (family : α → Cell) (region : α → Prop) (upper : ℚ)
    (hupper : upper ≤ 0)
    (hbound : ∀ θ, region θ → (family θ).turan ≤ upper) :
    ∀ θ, region θ → ¬ (family θ).Valid := by
  intro θ hθ
  exact Cell.not_valid_of_turan_nonpos (family θ)
    (le_trans (hbound θ hθ) hupper)

def positiveControl : Cell where
  leftEntry := 2
  middleEntry := 1
  rightEntry := 2
  nextDet := 3
  pivot := 1

theorem positiveControl_valid : positiveControl.Valid := by
  norm_num [positiveControl, Cell.Valid, Cell.turan]

theorem positiveControl_accepted : positiveControl.necessaryTest = true := by
  exact Cell.valid_necessaryTest positiveControl positiveControl_valid

def negativeControl : Cell where
  leftEntry := 1
  middleEntry := 2
  rightEntry := 1
  nextDet := 1
  pivot := 1

theorem negativeControl_rejected : negativeControl.necessaryTest = false := by
  norm_num [negativeControl, Cell.necessaryTest, Cell.turan]

theorem mixedControls_rejected :
    necessaryDodgsonTests [positiveControl, negativeControl] = false := by
  simp [necessaryDodgsonTests, positiveControl_accepted, negativeControl_rejected]

end RHFinitePruning.Dodgson
