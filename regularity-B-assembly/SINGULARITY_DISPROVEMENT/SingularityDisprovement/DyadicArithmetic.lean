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
    (Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1))).card = 2 ^ j := by
  rw [Nat.card_Ico, pow_succ]
  omega

theorem dyadicBlock_sum {j : ℕ} (hj : 1 ≤ j) :
    (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), dyadicAmplitude n) = 1 / (j : ℝ) := by
  classical
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = ∑ _n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)),
        1 / ((j : ℝ) * (2 : ℝ) ^ j) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact dyadicAmplitude_on_block hj (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2
    _ = (2 : ℝ) ^ j * (1 / ((j : ℝ) * (2 : ℝ) ^ j)) := by
      rw [Finset.sum_const, dyadicBlock_card]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = 1 / (j : ℝ) := by field_simp

theorem dyadicBlock_sum_sq {j : ℕ} (hj : 1 ≤ j) :
    (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), dyadicAmplitude n ^ 2) =
      1 / ((j : ℝ) ^ 2 * (2 : ℝ) ^ j) := by
  classical
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = ∑ _n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)),
        (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [dyadicAmplitude_on_block hj (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2]
    _ = (2 : ℝ) ^ j * (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      rw [Finset.sum_const, dyadicBlock_card]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
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
    (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), (n : ℝ) * dyadicAmplitude n ^ 2) =
      (3 - (2 : ℝ) ^ (- (j : ℤ))) / (2 * (j : ℝ) ^ 2) := by
  classical
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hle : (2 : ℕ) ^ j ≤ 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  calc
    _ = ∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)),
        (n : ℝ) * (1 / ((j : ℝ) * (2 : ℝ) ^ j)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [dyadicAmplitude_on_block hj (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2]
    _ = (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), (n : ℝ)) *
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
  gcongr <;> norm_num

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

theorem dyadicAmplitude_antitone_from_two {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    dyadicAmplitude n ≤ dyadicAmplitude m := by
  have hn : 2 ≤ n := hm.trans hmn
  have hlog : Nat.log 2 m ≤ Nat.log 2 n := Nat.log_mono_right hmn
  have hmpos : (0 : ℝ) < (Nat.log 2 m : ℝ) := by
    exact_mod_cast Nat.log_pos (by norm_num : 1 < (2 : ℕ)) hm
  rw [dyadicAmplitude, if_pos hn, dyadicAmplitude, if_pos hm]
  gcongr <;> norm_num

theorem dyadicAmplitude_condensed (j : ℕ) :
    (2 : ℝ) ^ j * dyadicAmplitude (2 ^ j) = 1 / (j : ℝ) := by
  by_cases hj : j = 0
  · subst j
    simp
  · have hj1 : 1 ≤ j := by omega
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    rw [dyadicAmplitude, if_pos (two_le_dyadic_pow hj1), Nat.log_pow (by norm_num)]
    have hp0 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp

theorem dyadicAmplitude_not_summable : ¬ Summable dyadicAmplitude := by
  intro hd
  have hm : ∀ᶠ n in atTop, dyadicAmplitude (n + 1) ≤ dyadicAmplitude n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact dyadicAmplitude_antitone_from_two hn (by omega)
  have hc := (summable_condensed_iff_of_eventually_nonneg
    (Filter.Eventually.of_forall dyadicAmplitude_nonneg) hm).mpr hd
  simp_rw [dyadicAmplitude_condensed] at hc
  exact Real.not_summable_one_div_natCast hc

theorem dyadicAmplitude_partialSums_tendsto_atTop :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, dyadicAmplitude n) atTop atTop := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg dyadicAmplitude_nonneg).mp
    dyadicAmplitude_not_summable

def dyadicR : ℝ := ∑' j : ℕ, 1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (j + 1))

def dyadicS : ℝ := ∑' j : ℕ,
  (3 - 1 / (2 : ℝ) ^ (j + 1)) / ((j + 1 : ℕ) : ℝ) ^ 2

private theorem positive_pseries_summable :
    Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ 2) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))

private theorem positive_pseries_sum_le_two :
    (∑' j : ℕ, 1 / ((j + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hfinite (N : ℕ) :
      (∑ j ∈ Finset.range N, 1 / ((j + 1 : ℕ) : ℝ) ^ 2) ≤
        2 - 2 / ((N + 1 : ℕ) : ℝ) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have hy : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
      have hxy : ((N + 2 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      have hstep : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤
          2 / ((N + 1 : ℕ) : ℝ) - 2 / ((N + 2 : ℕ) : ℝ) := by
        calc
          _ ≤ 2 / (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hx) (mul_pos hx hy)).mpr
            have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
            push_cast
            nlinarith
          _ = _ := by field_simp; push_cast; ring
      rw [Finset.sum_range_succ]
      have hidx : N.succ + 1 = N + 2 := by omega
      rw [hidx]
      linarith
  apply positive_pseries_summable.tsum_le_of_sum_range_le
  intro N
  exact (hfinite N).trans (sub_le_self _ (by positivity))

private theorem dyadicGeometric_hasSum :
    HasSum (fun j : ℕ => 1 / (2 : ℝ) ^ (j + 1)) 1 := by
  have h0 : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j) (1 - (1 / 2 : ℝ))⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have h1 : HasSum (fun j : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j)
      ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹) := h0.mul_left (1 / 2 : ℝ)
  have hnum : (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹ = 1 := by norm_num
  rw [hnum] at h1
  apply h1.congr
  intro j
  simp [pow_succ, one_div, mul_inv_rev, mul_comm]

private theorem dyadicR_term_nonneg (j : ℕ) :
    0 ≤ 1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (j + 1)) := by positivity

private theorem dyadicR_term_le (j : ℕ) :
    1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (j + 1)) ≤
      1 / (2 : ℝ) ^ (j + 1) := by
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 1)
  have hj2 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (j + 1)]

theorem dyadicR_bounds : 0 < dyadicR ∧ dyadicR < 1 := by
  have hs := Summable.of_nonneg_of_le dyadicR_term_nonneg dyadicR_term_le
    dyadicGeometric_hasSum.summable
  constructor
  · exact hs.tsum_pos dyadicR_term_nonneg 0 (by norm_num)
  · have hlt := Summable.tsum_lt_tsum_of_nonneg dyadicR_term_nonneg dyadicR_term_le
      (i := 1) (by norm_num) dyadicGeometric_hasSum.summable
    rw [dyadicGeometric_hasSum.tsum_eq] at hlt
    exact hlt

private theorem dyadicS_term_pos (j : ℕ) :
    0 < (3 - 1 / (2 : ℝ) ^ (j + 1)) / ((j + 1 : ℕ) : ℝ) ^ 2 := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hinv : 1 / (2 : ℝ) ^ (j + 1) ≤ 1 := (div_le_one (by positivity)).mpr hp
  apply div_pos _ (by positivity)
  linarith

private theorem dyadicS_term_lt (j : ℕ) :
    (3 - 1 / (2 : ℝ) ^ (j + 1)) / ((j + 1 : ℕ) : ℝ) ^ 2 <
      3 * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) := by
  rw [mul_one_div]
  apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
  have hp : (0 : ℝ) < 1 / (2 : ℝ) ^ (j + 1) := by positivity
  linarith

theorem dyadicS_bounds : 0 < dyadicS ∧ dyadicS < 6 := by
  have hg := positive_pseries_summable.mul_left 3
  have hs := Summable.of_nonneg_of_le (fun j => (dyadicS_term_pos j).le)
    (fun j => (dyadicS_term_lt j).le) hg
  constructor
  · exact hs.tsum_pos (fun j => (dyadicS_term_pos j).le) 0 (dyadicS_term_pos 0)
  · have hlt := Summable.tsum_lt_tsum_of_nonneg (fun j => (dyadicS_term_pos j).le)
      (fun j => (dyadicS_term_lt j).le) (i := 0) (dyadicS_term_lt 0) hg
    have hsum : (∑' j : ℕ, 3 * (1 / ((j + 1 : ℕ) : ℝ) ^ 2)) ≤ 6 := by
      rw [tsum_mul_left]
      linarith [positive_pseries_sum_le_two]
    exact hlt.trans_le hsum

/-- R05: the exact three block identities and the two convergent budget bounds. -/
theorem DYADIC_BLOCK_IDENTITIES :
    (∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), dyadicAmplitude n) = 1 / (j : ℝ)) ∧
    (∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), dyadicAmplitude n ^ 2) =
        1 / ((j : ℝ) ^ 2 * (2 : ℝ) ^ j)) ∧
    (∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), (n : ℝ) * dyadicAmplitude n ^ 2) =
        (3 - (2 : ℝ) ^ (- (j : ℤ))) / (2 * (j : ℝ) ^ 2)) ∧
    (0 < dyadicR ∧ dyadicR < 1) ∧ (0 < dyadicS ∧ dyadicS < 6) := by
  exact ⟨fun _ hj => dyadicBlock_sum hj, fun _ hj => dyadicBlock_sum_sq hj,
    fun _ hj => dyadicBlock_sum_weighted_sq hj, dyadicR_bounds, dyadicS_bounds⟩

theorem dyadicR_summable :
    Summable (fun j : ℕ => 1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (j + 1))) :=
  Summable.of_nonneg_of_le dyadicR_term_nonneg dyadicR_term_le dyadicGeometric_hasSum.summable

theorem dyadicS_summable :
    Summable (fun j : ℕ =>
      (3 - 1 / (2 : ℝ) ^ (j + 1)) / ((j + 1 : ℕ) : ℝ) ^ 2) :=
  Summable.of_nonneg_of_le (fun j => (dyadicS_term_pos j).le)
    (fun j => (dyadicS_term_lt j).le) (positive_pseries_summable.mul_left 3)

end
end SingularityDisprovement
