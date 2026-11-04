import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! Scoped reconstruction from the definition. This candidate has not yet
been externally compiled or audited. -/

namespace HVRSimpleMangoldtOne

theorem vonMangoldt_one : ArithmeticFunction.vonMangoldt 1 = 0 := by
  have h : ¬ IsPrimePow (1 : ℕ) := by
    intro h
    exact h.ne_one rfl
  change (if IsPrimePow (1 : ℕ) then Real.log (Nat.minFac 1) else 0) = 0
  rw [if_neg h]

end HVRSimpleMangoldtOne
