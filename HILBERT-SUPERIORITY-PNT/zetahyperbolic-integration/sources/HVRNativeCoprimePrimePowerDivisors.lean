import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

/-!
Scoped filtered divisor-set decomposition. Adapted from
Mathlib/Data/Nat/Factorization/PrimePow.lean, Copyright (c) 2022 Bhavik
Mehta, Apache License 2.0. It uses the more fundamental Mathlib theorem
`Nat.Coprime.isPrimePow_dvd_mul`; no transitive dependency independence is
claimed. This exact source requires an external Lean audit.
-/

namespace HVRNativeCoprimePrimePowerDivisors

theorem filtered_divisors_mul {a b : ℕ} (hab : a.Coprime b) :
    {d ∈ (a * b).divisors | IsPrimePow d} =
      {d ∈ a.divisors ∪ b.divisors | IsPrimePow d} := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul

end HVRNativeCoprimePrimePowerDivisors
