import Init

set_option autoImplicit false

namespace Tail16Bool

/-- Boolean conjunction elimination by cases, independent of theorem aliases. -/
theorem andTrue {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
      cases b with
      | false => cases h
      | true => exact ⟨rfl, rfl⟩

end Tail16Bool
