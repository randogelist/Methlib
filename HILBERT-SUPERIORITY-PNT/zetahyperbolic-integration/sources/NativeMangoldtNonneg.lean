import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
A candidate reconstruction of the pointwise nonnegativity of the actual
Mathlib von Mangoldt function.  This unfolds its prime-power definition and
uses positivity of the least prime factor and nonnegativity of the logarithm.
It does not invoke `ArithmeticFunction.vonMangoldt_nonneg` explicitly.

Status: source candidate only. No Lean compiler or theorem-level axiom audit
has been run on this file. The transitive declaration dependencies of the used
lemmas still require inspection; avoiding an identifier in source is not by
itself a proof that the entire dependency graph avoids it.
-/

namespace HVRNativeMangoldtNonneg

/-- Pointwise nonnegativity for the actual von Mangoldt arithmetic function. -/
theorem vonMangoldt_nonneg_native (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n := by
  change 0 ≤ (if IsPrimePow n then Real.log (Nat.minFac n) else 0)
  by_cases h : IsPrimePow n
  · rw [if_pos h]
    have hmin : 1 ≤ Nat.minFac n := Nat.minFac_pos n
    exact Real.log_nonneg (by exact_mod_cast hmin)
  · simp only [if_neg h, le_refl]

end HVRNativeMangoldtNonneg
