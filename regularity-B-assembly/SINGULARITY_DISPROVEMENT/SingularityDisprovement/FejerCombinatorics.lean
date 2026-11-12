import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! Finite nonnegative Toeplitz sums used by the physical Fejer test.
No regularity, Fourier-realization, or essential-supremum premise is hidden here.
-/

set_option autoImplicit false
set_option Elab.async true
open scoped BigOperators

namespace SingularityDisprovement
noncomputable section

def fejerCoefficientAverage (c : ℤ → ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, c ((k : ℤ) - (j : ℤ))) / (N : ℝ)

theorem positive_toeplitz_row_lower_bound
    (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (N j : ℕ) (hj : j < N) :
    (∑ n ∈ Finset.range N, c (n : ℤ)) ≤
      ∑ k ∈ Finset.range (2 * N), c ((k : ℤ) - (j : ℤ)) := by
  classical
  let S : Finset ℕ := (Finset.range N).image (fun n => j + n)
  have hsub : S ⊆ Finset.range (2 * N) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range] at hn ⊢
    omega
  have hsum : (∑ k ∈ S, c ((k : ℤ) - (j : ℤ))) =
      ∑ n ∈ Finset.range N, c (n : ℤ) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      congr 1
      push_cast
      ring
    · intro a ha b hb hab
      change j + a = j + b at hab
      exact Nat.add_left_cancel hab
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hc _)

theorem positive_toeplitz_double_lower_bound
    (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n) (N : ℕ) :
    (N : ℝ) * (∑ n ∈ Finset.range N, c (n : ℤ)) ≤
      ∑ j ∈ Finset.range (2 * N),
        ∑ k ∈ Finset.range (2 * N), c ((k : ℤ) - (j : ℤ)) := by
  calc
    _ = ∑ _j ∈ Finset.range N, ∑ n ∈ Finset.range N, c (n : ℤ) := by simp
    _ ≤ ∑ j ∈ Finset.range N,
        ∑ k ∈ Finset.range (2 * N), c ((k : ℤ) - (j : ℤ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact positive_toeplitz_row_lower_bound c hc N j (Finset.mem_range.mp hj)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro j hj hj'
        exact Finset.sum_nonneg (fun k hk => hc _)

theorem positive_fejerAverage_lower_bound
    (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n) (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.range N, c (n : ℤ)) / 2 ≤ fejerCoefficientAverage c (2 * N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold fejerCoefficientAverage
  push_cast
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))).mpr
  have heq : ((∑ n ∈ Finset.range N, c (n : ℤ)) / 2) * (2 * (N : ℝ)) =
      (N : ℝ) * (∑ n ∈ Finset.range N, c (n : ℤ)) := by ring
  rw [heq]
  exact positive_toeplitz_double_lower_bound c hc N

/-- Uniform boundedness of these positive Fejer averages forces absolute
summability of the nonnegative positive-index coefficients. -/
theorem summable_of_positive_fejerAverage_bounded
    (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, 0 < N → fejerCoefficientAverage c N ≤ B) :
    Summable (fun n : ℕ => c (n : ℤ)) := by
  apply summable_of_sum_range_le (c := 2 * B) (fun n => hc n)
  intro N
  by_cases hN : N = 0
  · simpa [hN] using (show (0 : ℝ) ≤ 2 * B by positivity)
  · have hpos : 0 < N := Nat.pos_of_ne_zero hN
    have hlow := positive_fejerAverage_lower_bound c hc N hpos
    have hhigh := hbound (2 * N) (by omega)
    linarith

theorem positive_fejerAverage_unbounded_of_not_summable
    (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hnot : ¬ Summable (fun n : ℕ => c (n : ℤ)))
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 0 < N ∧ B < fejerCoefficientAverage c N := by
  by_contra h
  push_neg at h
  exact hnot (summable_of_positive_fejerAverage_bounded c hc B hB h)

end
end SingularityDisprovement
