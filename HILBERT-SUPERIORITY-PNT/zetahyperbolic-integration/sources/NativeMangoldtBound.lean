import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
An elementary pointwise upper bound for the actual von Mangoldt function.

This source candidate unfolds the definition and compares the least prime
factor with the original natural number. It does not explicitly invoke the
original von Mangoldt nonnegativity, prime-value, power-value, divisor-sum,
or logarithmic-bound theorems. Compilation, axiom auditing, and recursive
declaration-dependency inspection remain necessary.
-/

namespace HVRNativeMangoldtBound

theorem vonMangoldt_le_log_native (n : ℕ) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) := by
  change (if IsPrimePow n then Real.log (Nat.minFac n) else 0) ≤
    Real.log (n : ℝ)
  by_cases hn : n = 0
  · subst n
    simp only [not_isPrimePow_zero, if_false, Nat.cast_zero, Real.log_zero, le_refl]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hpow : IsPrimePow n
    · rw [if_pos hpow]
      have hminpos : (0 : ℝ) < (Nat.minFac n : ℝ) := by
        exact_mod_cast Nat.minFac_pos n
      have hminle : (Nat.minFac n : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.minFac_le hnpos
      exact Real.log_le_log hminpos hminle
    · rw [if_neg hpow]
      apply Real.log_nonneg
      exact_mod_cast (Nat.succ_le_of_lt hnpos)

end HVRNativeMangoldtBound
