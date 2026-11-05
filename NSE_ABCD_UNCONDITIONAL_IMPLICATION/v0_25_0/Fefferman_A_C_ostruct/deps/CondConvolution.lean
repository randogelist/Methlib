import Mathlib

namespace CondFeffA

open scoped BigOperators

/-- A single diagonal written as an indicator on the ambient finite square. -/
private theorem diagonal_on_square (n k : ℕ) (hk : k ≤ n) (F : ℕ → ℕ → ℝ) :
    (∑ l ∈ Finset.range (k + 1), F l (k - l)) =
      ∑ l ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        if l + r = k then F l r else 0 := by
  calc
    (∑ l ∈ Finset.range (k + 1), F l (k - l)) =
        ∑ l ∈ Finset.range (k + 1), if l ≤ k then F l (k - l) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      have h := Finset.mem_range.mp hl
      simp [show l ≤ k by omega]
    _ = ∑ l ∈ Finset.range (n + 1), if l ≤ k then F l (k - l) else 0 := by
      apply Finset.sum_subset
      · intro l hl
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hl) (by omega))
      · intro l _ hl
        have h : ¬ l ≤ k := fun hle => hl (Finset.mem_range.mpr (by omega))
        simp [h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : l ≤ k
      · rw [if_pos h]
        symm
        rw [Finset.sum_eq_single (k - l)]
        · simp [show l + (k - l) = k by omega]
        · intro r _ hr
          simp [show l + r ≠ k by omega]
        · intro hn
          exact False.elim (hn (Finset.mem_range.mpr (by omega)))
      · rw [if_neg h]
        symm
        apply Finset.sum_eq_zero
        intro r _
        simp [show l + r ≠ k by omega]

/-- Reindex a triangular Cauchy convolution by the independent amplitude
indices. Neither the order of the rows nor the truncation changes. -/
theorem triangular_convolution (n : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1), F l (k - l)) =
      ∑ l ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        if l + r ≤ n then F l r else 0 := by
  let S := Finset.range (n + 1)
  let T := fun k l r : ℕ => if l + r = k then F l r else 0
  calc
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1), F l (k - l))
      = ∑ k ∈ S, ∑ l ∈ S, ∑ r ∈ S, T k l r := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k < n + 1 := Finset.mem_range.mp hk
          exact diagonal_on_square n k (by omega) F
    _ = ∑ l ∈ S, ∑ k ∈ S, ∑ r ∈ S, T k l r := Finset.sum_comm
    _ = ∑ l ∈ S, ∑ r ∈ S, ∑ k ∈ S, T k l r := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro r hr
      simp [T, S, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

end CondFeffA

#print axioms CondFeffA.triangular_convolution
