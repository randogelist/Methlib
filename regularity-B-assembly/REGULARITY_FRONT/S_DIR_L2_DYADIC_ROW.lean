import S_DIR_L2_DYADIC_SCHUR

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2: Infinite dyadic majorant and conditional geometric row adapter

No change to the frozen physical theorem or its hypotheses.

The first three theorems close the infinite-sum passage for the exact
unconditional dyadic rational sequence from v0.4.1. The remaining theorems
reduce the actual directional-plane kernel to finite shells. Their finite-shell
partition is an explicit premise, not an axiom or a claimed proof of the full
rank-two infinite lattice row bound.
-/

/-- The certified dyadic kernel consists of nonnegative real terms. -/
theorem S_DIR_L2_DYADIC_KERNEL_TERM_NONNEG (r : ℝ) (j : ℕ) :
    0 ≤ dyadicKernelTerm r j := by
  unfold dyadicKernelTerm
  positivity

/-- All dyadic kernel prefixes have bounded sum, hence the infinite series exists. -/
theorem S_DIR_L2_DYADIC_KERNEL_SUMMABLE
    (r : ℝ) (hr : 0 < r) :
    Summable (dyadicKernelTerm r) := by
  apply summable_of_sum_range_le
  · intro j
    exact S_DIR_L2_DYADIC_KERNEL_TERM_NONNEG r j
  · intro N
    exact S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND r hr N

/-- The infinite dyadic majorant has exactly the bound used by the Schur route. -/
theorem S_DIR_L2_DYADIC_KERNEL_TSUM_BOUND
    (r : ℝ) (hr : 0 < r) :
    (∑' j : ℕ, dyadicKernelTerm r j) ≤ 4 / r := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact S_DIR_L2_DYADIC_KERNEL_TERM_NONNEG r j
  · intro N
    exact S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND r hr N

/-- An unconditional general real-series endpoint: bounded finite sums
    imply convergence and the same bound for the infinite sum. -/
theorem S_DIR_L2_INFINITE_ROW_FROM_ALL_FINITE_BOUNDS
    {ι : Type*} (f : ι → ℝ) (C : ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hF : ∀ F : Finset ι, (∑ i ∈ F, f i) ≤ C) :
    Summable f ∧ (∑' i, f i) ≤ C := by
  exact ⟨summable_of_sum_le hf hF, Real.tsum_le_of_sum_le hf hF⟩

/-- The unnormalized positive radial kernel appearing in the time-integrated
    heat-kernel correlation. Zero mode remains excluded in applications. -/
def directionalRadialRowTerm (r : ℝ) (k : Mode3) : ℝ :=
  let s := Real.sqrt (latticeRadiusSq k)
  1 / (s * (r ^ 2 + s ^ 2))

/-- At radius at least `2^j`, the correlation term is bounded by the
    corresponding dyadic shell majorant. -/
theorem S_DIR_L2_DYADIC_ROW_POINTWISE
    (r : ℝ) (hr : 0 < r) (j : ℕ) (k : Mode3)
    (hlower : (2 : ℝ) ^ j ≤ Real.sqrt (latticeRadiusSq k)) :
    directionalRadialRowTerm r k ≤
      1 / ((2 : ℝ) ^ j * (r ^ 2 + ((2 : ℝ) ^ j) ^ 2)) := by
  let q : ℝ := (2 : ℝ) ^ j
  let s : ℝ := Real.sqrt (latticeRadiusSq k)
  have hq : 0 < q := by dsimp [q]; positivity
  have hs : 0 < s := lt_of_lt_of_le hq hlower
  have hqs : q ≤ s := hlower
  have hsq : q ^ 2 ≤ s ^ 2 := by
    have hprod : 0 ≤ (s - q) * (s + q) :=
      mul_nonneg (sub_nonneg.mpr hqs) (add_nonneg hs.le hq.le)
    nlinarith
  have hden : q * (r ^ 2 + q ^ 2) ≤ s * (r ^ 2 + s ^ 2) := by
    calc
      q * (r ^ 2 + q ^ 2) ≤ s * (r ^ 2 + q ^ 2) :=
        mul_le_mul_of_nonneg_right hqs (by positivity)
      _ ≤ s * (r ^ 2 + s ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hs.le
  change 1 / (s * (r ^ 2 + s ^ 2)) ≤ 1 / (q * (r ^ 2 + q ^ 2))
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa using hden

/-- Any finite shell with the certified plane-count budget obeys its
    `16 * dyadicKernelTerm` majorization. -/
theorem S_DIR_L2_DYADIC_FINITE_SHELL_BUDGET
    (r : ℝ) (hr : 0 < r) (j : ℕ)
    (F : Finset Mode3)
    (hcard : (F.card : ℝ) ≤ 16 * (((2 : ℝ) ^ j) ^ 2))
    (hlower : ∀ k ∈ F,
      (2 : ℝ) ^ j ≤ Real.sqrt (latticeRadiusSq k)) :
    (∑ k ∈ F, directionalRadialRowTerm r k) ≤
      16 * dyadicKernelTerm r j := by
  let q : ℝ := (2 : ℝ) ^ j
  have hq : 0 < q := by dsimp [q]; positivity
  have hden : 0 < r ^ 2 + q ^ 2 := by positivity
  have hMajor : ∀ k ∈ F,
      directionalRadialRowTerm r k ≤ 1 / (q * (r ^ 2 + q ^ 2)) := by
    intro k hk
    exact S_DIR_L2_DYADIC_ROW_POINTWISE r hr j k (hlower k hk)
  calc
    (∑ k ∈ F, directionalRadialRowTerm r k) ≤
        (∑ _k ∈ F, 1 / (q * (r ^ 2 + q ^ 2))) := by
          exact Finset.sum_le_sum hMajor
    _ = (F.card : ℝ) * (1 / (q * (r ^ 2 + q ^ 2))) := by simp
    _ ≤ (16 * q ^ 2) * (1 / (q * (r ^ 2 + q ^ 2))) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [q] using hcard
      · positivity
    _ = 16 * dyadicKernelTerm r j := by
      dsimp [dyadicKernelTerm, q]
      have hq0 : (2 : ℝ) ^ j ≠ 0 := by positivity
      have hd0 : r ^ 2 + ((2 : ℝ) ^ j) ^ 2 ≠ 0 := by positivity
      field_simp [hq0, hd0]

/-- The previously certified plane counting lemma feeds the finite shell
    majorant without changing its numerical constant. -/
theorem S_DIR_L2_DYADIC_PLANE_FINITE_SHELL_BUDGET
    (a : Mode3) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r) (j : ℕ)
    (F : Finset Mode3)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hupper : ∀ k ∈ F,
      latticeRadiusSq k < (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) ^ 2)
    (hlower : ∀ k ∈ F,
      (2 : ℝ) ^ j ≤ Real.sqrt (latticeRadiusSq k)) :
    (∑ k ∈ F, directionalRadialRowTerm r k) ≤
      16 * dyadicKernelTerm r j := by
  have hcount := S_DIR_L2_DYADIC_PLANE_BALL_CARD
    a ha F j hplane hupper
  have hreal : (F.card : ℝ) ≤ 16 * (((2 : ℝ) ^ j) ^ 2) := by
    exact_mod_cast hcount
  exact S_DIR_L2_DYADIC_FINITE_SHELL_BUDGET
    r hr j F hreal hlower

/-- Conditional geometric partition-to-row edge. Only the precise finite
    shell partition and radial support assumptions remain as premises.
    All finite shell bounds and dyadic summations are proved internally. -/
theorem S_DIR_L2_FINITE_ROW_OF_DYADIC_SHELL_PARTITION
    (a : Mode3) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (F : Finset Mode3) (N : ℕ)
    (shell : ℕ → Finset Mode3)
    (hpart : F = (Finset.range N).biUnion shell)
    (hdisjoint : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint shell)
    (hplane : ∀ j ∈ Finset.range N,
      ∀ k ∈ shell j, directionalDot a k = 0)
    (hupper : ∀ j ∈ Finset.range N,
      ∀ k ∈ shell j,
        latticeRadiusSq k < (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) ^ 2)
    (hlower : ∀ j ∈ Finset.range N,
      ∀ k ∈ shell j,
        (2 : ℝ) ^ j ≤ Real.sqrt (latticeRadiusSq k)) :
    (∑ k ∈ F, directionalRadialRowTerm r k) ≤ 64 / r := by
  classical
  rw [hpart, Finset.sum_biUnion hdisjoint]
  calc
    (∑ j ∈ Finset.range N,
      ∑ k ∈ shell j, directionalRadialRowTerm r k)
        ≤ ∑ j ∈ Finset.range N, 16 * dyadicKernelTerm r j := by
          apply Finset.sum_le_sum
          intro j hj
          exact S_DIR_L2_DYADIC_PLANE_FINITE_SHELL_BUDGET
            a ha r hr j (shell j)
            (hplane j hj) (hupper j hj) (hlower j hj)
    _ = 16 * (∑ j ∈ Finset.range N, dyadicKernelTerm r j) := by
      rw [Finset.mul_sum]
    _ ≤ 16 * (4 / r) := by
      exact mul_le_mul_of_nonneg_left
        (S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND r hr N) (by norm_num)
    _ = 64 / r := by ring

end SDirL2
