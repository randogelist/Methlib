import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators Topology
open Filter

namespace SingularityDisprovement

noncomputable section

/-- The literal coefficients, with the two absent modes completed by zero. -/
def dyadicAmplitude (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((Nat.log 2 n : ℝ) * (2 : ℝ) ^ Nat.log 2 n) else 0

@[simp] theorem dyadicAmplitude_zero : dyadicAmplitude 0 = 0 := by
  norm_num [dyadicAmplitude]

@[simp] theorem dyadicAmplitude_one : dyadicAmplitude 1 = 0 := by
  norm_num [dyadicAmplitude]

@[simp] theorem dyadicAmplitude_two : dyadicAmplitude 2 = 1 / 2 := by
  norm_num [dyadicAmplitude, Nat.log_eq_one_iff']

theorem dyadicAmplitude_nonneg (n : ℕ) : 0 ≤ dyadicAmplitude n := by
  unfold dyadicAmplitude
  split_ifs <;> positivity

theorem dyadicAmplitude_pos {n : ℕ} (hn : 2 ≤ n) : 0 < dyadicAmplitude n := by
  have hj : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) hn
  rw [dyadicAmplitude, if_pos hn]
  positivity

theorem two_le_dyadic_pow {j : ℕ} (hj : 1 ≤ j) : 2 ≤ 2 ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [pow_succ]
  have hp : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
  omega

theorem dyadicAmplitude_on_block {j n : ℕ} (hj : 1 ≤ j)
    (hlo : 2 ^ j ≤ n) (hhi : n < 2 ^ (j + 1)) :
    dyadicAmplitude n = 1 / ((j : ℝ) * (2 : ℝ) ^ j) := by
  have hn : 2 ≤ n := (two_le_dyadic_pow hj).trans hlo
  have hlog : Nat.log 2 n = j := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  simp [dyadicAmplitude, hn, hlog]

theorem dyadicBlock_card (j : ℕ) :
    (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card = 2 ^ j := by
  rw [Nat.card_Ico, pow_succ]
  omega

theorem dyadicBlock_sum {j : ℕ} (hj : 1 ≤ j) :
    (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), dyadicAmplitude n) = 1 / (j : ℝ) := by
  classical
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = ∑ _n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
        1 / ((j : ℝ) * (2 : ℝ) ^ j) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact dyadicAmplitude_on_block hj (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2
    _ = (2 : ℝ) ^ j * (1 / ((j : ℝ) * (2 : ℝ) ^ j)) := by
      simp [dyadicBlock_card]
    _ = 1 / (j : ℝ) := by field_simp

theorem dyadicBlock_sum_sq {j : ℕ} (hj : 1 ≤ j) :
    (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), dyadicAmplitude n ^ 2) =
      1 / ((j : ℝ) ^ 2 * (2 : ℝ) ^ j) := by
  classical
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = ∑ _n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
        (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [dyadicAmplitude_on_block hj (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2]
    _ = (2 : ℝ) ^ j * (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      simp [dyadicBlock_card]
    _ = _ := by field_simp

private theorem sum_range_cast_real (N : ℕ) :
    (∑ n ∈ Finset.range N, (n : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_Ico_cast_real {lo hi : ℕ} (h : lo ≤ hi) :
    (∑ n ∈ Finset.Ico lo hi, (n : ℝ)) =
      ((hi : ℝ) * ((hi : ℝ) - 1) - (lo : ℝ) * ((lo : ℝ) - 1)) / 2 := by
  have hs := Finset.sum_range_add_sum_Ico (fun n : ℕ => (n : ℝ)) h
  rw [sum_range_cast_real, sum_range_cast_real] at hs
  linarith

theorem dyadicBlock_sum_weighted_sq {j : ℕ} (hj : 1 ≤ j) :
    (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (n : ℝ) * dyadicAmplitude n ^ 2) =
      (3 - (2 : ℝ) ^ (- (j : ℤ))) / (2 * (j : ℝ) ^ 2) := by
  classical
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hle : (2 : ℕ) ^ j ≤ 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  calc
    _ = ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
        (n : ℝ) * (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [dyadicAmplitude_on_block hj (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2]
    _ = (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (n : ℝ)) *
        (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [sum_Ico_cast_real hle]
      push_cast
      rw [pow_succ, zpow_neg, zpow_natCast]
      field_simp
      <;> ring

/-- Monotone majorant used only for summability of the exact dyadic coefficients. -/
def dyadicSquareMajorant (n : ℕ) : ℝ :=
  1 / (((max 1 (Nat.log 2 n) : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ Nat.log 2 n)

theorem dyadicSquareMajorant_nonneg (n : ℕ) : 0 ≤ dyadicSquareMajorant n := by
  unfold dyadicSquareMajorant
  positivity

theorem dyadicSquareMajorant_antitone : Antitone dyadicSquareMajorant := by
  intro m n hmn
  have hlog : Nat.log 2 m ≤ Nat.log 2 n := Nat.log_mono_right hmn
  unfold dyadicSquareMajorant
  gcongr

theorem dyadicSquareMajorant_condensed (j : ℕ) :
    (2 : ℝ) ^ j * dyadicSquareMajorant (2 ^ j) =
      1 / (((max 1 j : ℕ) : ℝ) ^ 2) := by
  rw [dyadicSquareMajorant, Nat.log_pow (by norm_num)]
  have hp : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hj : ((max 1 j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show max 1 j ≠ 0 by omega)
  field_simp

theorem dyadicSquareMajorant_summable : Summable dyadicSquareMajorant := by
  apply (summable_condensed_iff_of_nonneg dyadicSquareMajorant_nonneg
    (fun _m _n _hm hmn => dyadicSquareMajorant_antitone hmn)).mp
  simp_rw [dyadicSquareMajorant_condensed]
  apply (summable_nat_add_iff 1).mp
  have hp : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp' := (summable_nat_add_iff 1).mpr hp
  apply hp'.congr
  intro j
  have hj : 1 ≤ j + 1 := by omega
  simp [max_eq_right hj]

theorem dyadicAmplitude_weighted_sq_le (n : ℕ) :
    (n : ℝ) * dyadicAmplitude n ^ 2 ≤ 2 * dyadicSquareMajorant n := by
  by_cases hn : 2 ≤ n
  · have hj : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
    have hjR : (0 : ℝ) < (Nat.log 2 n : ℝ) := by exact_mod_cast hj
    have hpR : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n := by positivity
    have hnlt : (n : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 n := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
      exact_mod_cast (by simpa [pow_succ, mul_comm] using h)
    rw [dyadicAmplitude, if_pos hn, dyadicSquareMajorant, max_eq_right hj]
    have heqL : (n : ℝ) * (1 / ((Nat.log 2 n : ℝ) * (2 : ℝ) ^ Nat.log 2 n)) ^ 2 =
        (n : ℝ) / ((Nat.log 2 n : ℝ) ^ 2 * ((2 : ℝ) ^ Nat.log 2 n) ^ 2) := by ring
    have heqR : 2 * (1 / ((Nat.log 2 n : ℝ) ^ 2 * (2 : ℝ) ^ Nat.log 2 n)) =
        (2 * (2 : ℝ) ^ Nat.log 2 n) /
          ((Nat.log 2 n : ℝ) ^ 2 * ((2 : ℝ) ^ Nat.log 2 n) ^ 2) := by
      field_simp
      <;> ring
    rw [heqL, heqR]
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr hnlt.le
  · rw [dyadicAmplitude, if_neg hn]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (dyadicSquareMajorant_nonneg n)

theorem dyadicAmplitude_weighted_sq_summable :
    Summable (fun n : ℕ => (n : ℝ) * dyadicAmplitude n ^ 2) := by
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    dyadicAmplitude_weighted_sq_le (dyadicSquareMajorant_summable.mul_left 2)

theorem dyadicAmplitude_sq_summable : Summable (fun n : ℕ => dyadicAmplitude n ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ dyadicAmplitude_weighted_sq_summable
  intro n
  by_cases hn : 2 ≤ n
  · have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith [sq_nonneg (dyadicAmplitude n)]
  · simp [dyadicAmplitude, hn]

end
end SingularityDisprovement
