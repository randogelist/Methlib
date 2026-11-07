import Std

/-!
Finite Boolean pruning with explicit accepted-witness preservation.
Root soundness does not require the preservation premise.
-/

set_option autoImplicit false

namespace RHFinitePruning

universe u

variable {α : Type u}

/-- The presieve executes before the original checker. -/
def checkPruned (keep check : α → Bool) (w : α) : Bool :=
  keep w && check w

private theorem and_true_iff (b c : Bool) :
    ((b && c) = true) ↔ b = true ∧ c = true := by
  cases b <;> cases c <;> simp

theorem checkPruned_accepts_keep
    (keep check : α → Bool) (w : α)
    (h : checkPruned keep check w = true) :
    keep w = true := by
  exact ((and_true_iff (keep w) (check w)).mp h).1

theorem checkPruned_accepts_check
    (keep check : α → Bool) (w : α)
    (h : checkPruned keep check w = true) :
    check w = true := by
  exact ((and_true_iff (keep w) (check w)).mp h).2

/-- Any original root conclusion remains sound after pruning. -/
theorem checkPruned_sound
    (keep check : α → Bool) (P : Prop)
    (sound : ∀ w : α, check w = true → P)
    (w : α) (h : checkPruned keep check w = true) : P := by
  exact sound w (checkPruned_accepts_check keep check w h)

/-- Pointwise conclusions also transfer through the same Boolean wrapper. -/
theorem checkPruned_sound_at
    (keep check : α → Bool) (P : α → Prop)
    (sound : ∀ w : α, check w = true → P w)
    (w : α) (h : checkPruned keep check w = true) : P w := by
  exact sound w (checkPruned_accepts_check keep check w h)

/-- The necessity premise guarantees that no accepted witness is removed. -/
theorem checkPruned_eq_check
    (keep check : α → Bool)
    (necessary : ∀ w : α, check w = true → keep w = true)
    (w : α) :
    checkPruned keep check w = check w := by
  cases hc : check w with
  | false =>
      cases hk : keep w <;> simp [checkPruned, hc, hk]
  | true =>
      have hk : keep w = true := necessary w hc
      simp [checkPruned, hc, hk]

theorem checkPruned_eq
    (keep check : α → Bool)
    (necessary : ∀ w : α, check w = true → keep w = true) :
    checkPruned keep check = check := by
  funext w
  exact checkPruned_eq_check keep check necessary w

theorem checkPruned_accept_iff
    (keep check : α → Bool)
    (necessary : ∀ w : α, check w = true → keep w = true)
    (w : α) :
    checkPruned keep check w = true ↔ check w = true := by
  rw [checkPruned_eq_check keep check necessary w]

theorem checkPruned_exists_iff
    (keep check : α → Bool)
    (necessary : ∀ w : α, check w = true → keep w = true) :
    (∃ w : α, checkPruned keep check w = true) ↔
      ∃ w : α, check w = true := by
  constructor
  · intro h
    rcases h with ⟨w, hw⟩
    exact ⟨w, checkPruned_accepts_check keep check w hw⟩
  · intro h
    rcases h with ⟨w, hw⟩
    exact ⟨w, (checkPruned_accept_iff keep check necessary w).mpr hw⟩

theorem checkPruned_false_of_keep_false
    (keep check : α → Bool) (w : α)
    (hReject : keep w = false) :
    checkPruned keep check w = false := by
  simp [checkPruned, hReject]

/-- A proved necessary-condition failure excludes original acceptance. -/
theorem check_false_of_keep_false
    (keep check : α → Bool)
    (necessary : ∀ w : α, check w = true → keep w = true)
    (w : α) (hReject : keep w = false) :
    check w = false := by
  cases hc : check w with
  | false => rfl
  | true =>
      have hk : keep w = true := necessary w hc
      rw [hReject] at hk
      cases hk

end RHFinitePruning
