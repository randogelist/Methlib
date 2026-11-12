import Mathlib

/-!
Finite weighted Schur inequality and the exact numerical admission bridge.
The infinite lattice row estimate is not assumed proved by this module.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuasiFeffermanB
noncomputable section

/-- Weighted two-variable inequality used in the Schur test. -/
theorem WEIGHTED_SCHUR_PAIR
    (x y u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * x * y ≤ x ^ 2 * (v / u) + y ^ 2 * (u / v) := by
  apply (mul_le_mul_iff_right₀ (mul_pos hu hv)).mp
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hv0 : v ≠ 0 := ne_of_gt hv
  field_simp [hu0, hv0]
  nlinarith [sq_nonneg (x * v - y * u)]

/-- Finite weighted Schur test with an explicitly supplied matrix row bound.
This is independent of the analytic proof of a particular lattice row bound. -/
theorem FINITE_WEIGHTED_SCHUR
    {ι : Type*} (s : Finset ι) (M : ι → ι → ℝ) (w x : ι → ℝ) (C : ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ M i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, M i j = M j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, M i j * w j) ≤ C * w i) :
    (∑ i ∈ s, ∑ j ∈ s, M i j * x i * x j) ≤ C * ∑ i ∈ s, x i ^ 2 := by
  let A : ℝ := ∑ i ∈ s, (x i ^ 2 / w i) * (∑ j ∈ s, M i j * w j)
  have hA : A ≤ C * ∑ i ∈ s, x i ^ 2 := by
    calc
      A ≤ ∑ i ∈ s, (x i ^ 2 / w i) * (C * w i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi)
          (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = C * ∑ i ∈ s, x i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [ne_of_gt (hw i hi)]
        <;> ring
  have hfirst :
      (∑ i ∈ s, ∑ j ∈ s, M i j * (x i ^ 2 * (w j / w i))) = A := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsecond :
      (∑ i ∈ s, ∑ j ∈ s, M i j * (x j ^ 2 * (w i / w j))) = A := by
    rw [Finset.sum_comm]
    calc
      (∑ j ∈ s, ∑ i ∈ s, M i j * (x j ^ 2 * (w i / w j))) =
          ∑ j ∈ s, ∑ i ∈ s, M j i * (x j ^ 2 * (w i / w j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsym i hi j hj]
      _ = A := hfirst
  have htwice :
      2 * (∑ i ∈ s, ∑ j ∈ s, M i j * x i * x j) ≤ A + A := by
    calc
      2 * (∑ i ∈ s, ∑ j ∈ s, M i j * x i * x j) =
          ∑ i ∈ s, ∑ j ∈ s, M i j * (2 * x i * x j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i ∈ s, ∑ j ∈ s,
          M i j * (x i ^ 2 * (w j / w i) + x j ^ 2 * (w i / w j)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (WEIGHTED_SCHUR_PAIR (x i) (x j) (w i) (w j) (hw i hi) (hw j hj))
          (hM i hi j hj)
      _ = A + A := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [hfirst, hsecond]
  linarith

/-- Finite weighted Schur test with a mode-dependent diagonal majorant. -/
theorem FINITE_WEIGHTED_SCHUR_DIAGONAL
    {ι : Type*} (s : Finset ι) (M : ι → ι → ℝ) (w x d : ι → ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ M i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, M i j = M j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, M i j * w j) ≤ d i * w i) :
    (∑ i ∈ s, ∑ j ∈ s, M i j * x i * x j) ≤ ∑ i ∈ s, d i * x i ^ 2 := by
  let A : ℝ := ∑ i ∈ s, (x i ^ 2 / w i) * (∑ j ∈ s, M i j * w j)
  have hA : A ≤ ∑ i ∈ s, d i * x i ^ 2 := by
    calc
      A ≤ ∑ i ∈ s, (x i ^ 2 / w i) * (d i * w i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi)
          (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = ∑ i ∈ s, d i * x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [ne_of_gt (hw i hi)]
        <;> ring
  have hfirst :
      (∑ i ∈ s, ∑ j ∈ s, M i j * (x i ^ 2 * (w j / w i))) = A := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsecond :
      (∑ i ∈ s, ∑ j ∈ s, M i j * (x j ^ 2 * (w i / w j))) = A := by
    rw [Finset.sum_comm]
    calc
      (∑ j ∈ s, ∑ i ∈ s, M i j * (x j ^ 2 * (w i / w j))) =
          ∑ j ∈ s, ∑ i ∈ s, M j i * (x j ^ 2 * (w i / w j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsym i hi j hj]
      _ = A := hfirst
  have htwice :
      2 * (∑ i ∈ s, ∑ j ∈ s, M i j * x i * x j) ≤ A + A := by
    calc
      2 * (∑ i ∈ s, ∑ j ∈ s, M i j * x i * x j) =
          ∑ i ∈ s, ∑ j ∈ s, M i j * (2 * x i * x j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i ∈ s, ∑ j ∈ s,
          M i j * (x i ^ 2 * (w j / w i) + x j ^ 2 * (w i / w j)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (WEIGHTED_SCHUR_PAIR (x i) (x j) (w i) (w j) (hw i hi) (hw j hj))
          (hM i hi j hj)
      _ = A + A := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [hfirst, hsecond]
  linarith

/-- Exact weak-Schur-to-strict-caloric numerical implication on the unit torus.
The input Q²≤H/(4π) remains an explicit estimate to be supplied by the lattice
analysis; the critical radius and strictness are established here. -/
theorem STRICT_H12_TO_CALORIC_SQUARE
    (H Q ν : ℝ)
    (hSchur : Q ^ 2 ≤ H / (4 * Real.pi))
    (hsmall : H < 2 * Real.pi * ν ^ 2) :
    Q ^ 2 < ν ^ 2 / 2 := by
  have hden : 0 < 4 * Real.pi := by positivity
  have hscaled := (le_div_iff₀ hden).mp hSchur
  have hstrict : (4 * Real.pi) * Q ^ 2 <
      (4 * Real.pi) * (ν ^ 2 / 2) := by
    nlinarith
  exact (mul_lt_mul_iff_left₀ hden).mp (by simpa only [mul_comm] using hstrict)

end
end QuasiFeffermanB
