import SingularityDisprovement.DyadicArithmetic

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators Topology
open Filter

namespace SingularityDisprovement
noncomputable section

private theorem dyadic_partial_block_sum (f : ℕ → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 0)
    (J : ℕ) :
    (∑ n ∈ Finset.range (2 ^ (J + 1)), f n) =
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), f n := by
  induction J with
  | zero => simp [Finset.sum_range_succ, h0, h1]
  | succ J ih =>
      have hle : (2 : ℕ) ^ (J + 1) ≤ 2 ^ (J + 2) := by
        rw [show J + 2 = (J + 1) + 1 by omega, pow_succ]
        omega
      have hsplit := Finset.sum_range_add_sum_Ico f hle
      rw [ih] at hsplit
      simpa only [Finset.sum_range_succ, Nat.succ_eq_add_one, Nat.add_assoc] using hsplit.symm

private theorem dyadic_tsum_blocks (f : ℕ → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hf : Summable f)
    (hb : Summable (fun j : ℕ =>
      ∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), f n)) :
    (∑' n, f n) = ∑' j : ℕ,
      ∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), f n := by
  have hp : Tendsto (fun J : ℕ => (2 : ℕ) ^ (J + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hleft := hf.hasSum.tendsto_sum_nat.comp hp
  have hright := hb.hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hleft
  convert hright using 1
  ext J
  exact dyadic_partial_block_sum f h0 h1 J

theorem dyadicAmplitude_sq_tsum : (∑' n : ℕ, dyadicAmplitude n ^ 2) = dyadicR := by
  have hb (j : ℕ) :
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), dyadicAmplitude n ^ 2) =
        1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (j + 1)) := by
    simpa only [Nat.add_assoc] using dyadicBlock_sum_sq (j := j + 1) (by omega)
  have hs : Summable (fun j : ℕ =>
      ∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), dyadicAmplitude n ^ 2) :=
    dyadicR_summable.congr (fun j => (hb j).symm)
  rw [dyadic_tsum_blocks _ (by simp) (by simp) dyadicAmplitude_sq_summable hs]
  exact tsum_congr hb

theorem dyadicAmplitude_weighted_sq_tsum :
    (∑' n : ℕ, (n : ℝ) * dyadicAmplitude n ^ 2) = dyadicS / 2 := by
  have hb (j : ℕ) :
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), (n : ℝ) * dyadicAmplitude n ^ 2) =
        ((3 - 1 / (2 : ℝ) ^ (j + 1)) / ((j + 1 : ℕ) : ℝ) ^ 2) / 2 := by
    have h := dyadicBlock_sum_weighted_sq (j := j + 1) (by omega)
    simpa only [Nat.add_assoc, zpow_neg, zpow_natCast, one_div, div_div,
      mul_comm (2 : ℝ)] using h
  have hs : Summable (fun j : ℕ =>
      ∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)), (n : ℝ) * dyadicAmplitude n ^ 2) :=
    (dyadicS_summable.div_const 2).congr (fun j => (hb j).symm)
  rw [dyadic_tsum_blocks _ (by simp) (by simp) dyadicAmplitude_weighted_sq_summable hs]
  rw [show (∑' j : ℕ, ∑ n ∈ Finset.Ico ((2 : ℕ) ^ (j + 1)) (2 ^ (j + 2)),
        (n : ℝ) * dyadicAmplitude n ^ 2) =
      ∑' j : ℕ, ((3 - 1 / (2 : ℝ) ^ (j + 1)) / ((j + 1 : ℕ) : ℝ) ^ 2) / 2 from tsum_congr hb]
  rw [tsum_div_const]

end
end SingularityDisprovement
