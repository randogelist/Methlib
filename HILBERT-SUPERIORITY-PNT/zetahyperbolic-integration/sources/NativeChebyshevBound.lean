import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
Finite-product proof of the elementary bound on Chebyshev's theta function.
The odd binomial row bounds its equal middle coefficients using their sum.
Primes in the upper interval divide the binomial coefficient and therefore
bound the ratio of the two primorials.

Portions adapted from Mathlib4, revision
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0, under Apache-2.0:
* NumberTheory/Primorial.lean, copyright 2020 Patrick Stevens (authors
  Patrick Stevens, Yury Kudryashov, Bhavik Mehta);
* NumberTheory/Chebyshev.lean, copyright 2025 Alastair Irving (authors
  Alastair Irving, Terry Tao, Ruben Van de Velde).
See LICENSE-MATHLIB.txt.
-/

noncomputable section

namespace HVRNativeChebyshevBound

open Finset Nat

private theorem interval_prime_product_bound {m n : ℕ} (hnm : n ≤ m) :
    primorial (m + n) ≤ primorial m * (m + n).choose m := by
  let block := (Ico (m + 1) (m + n + 1)).filter Nat.Prime
  have hsplit : primorial (m + n) = primorial m * ∏ p ∈ block, p := by
    dsimp only [block]
    simp_rw [primorial, ← Ico_zero_eq_range]
    rw [← prod_union, ← filter_union, Ico_union_Ico_eq_Ico]
    exacts [Nat.zero_le _, by omega, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]
  have hd : (∏ p ∈ block, p) ∣ (m + n).choose m := by
    refine prod_primes_dvd _ (fun _ hp => (mem_filter.1 hp).2.prime) ?_
    intro p hp
    change p ∈ (Ico (m + 1) (m + n + 1)).filter Nat.Prime at hp
    rw [mem_filter, mem_Ico] at hp
    exact hp.2.dvd_choose_add hp.1.1 (hnm.trans_lt (m.lt_succ_self.trans_le hp.1.1))
      (Nat.lt_succ_iff.1 hp.1.2)
  rw [hsplit]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.choose_pos (Nat.le_add_right _ _)) hd)

private theorem odd_middle_bound (m : ℕ) : (2 * m + 1).choose m ≤ 4 ^ m := by
  have hp : (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) ≤
      ∑ j ∈ range ((2 * m + 1) + 1), (2 * m + 1).choose j :=
    Finset.add_le_sum (s := range ((2 * m + 1) + 1)) (i := m) (j := m + 1)
      (f := fun j => (2 * m + 1).choose j) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) (by omega)
  have hsym : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m :=
    Nat.choose_symm_of_eq_add (by omega)
  have hpow : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul, mul_comm] <;> rfl
  rw [hsym, Nat.sum_range_choose, hpow] at hp
  omega

/-- Elementary primorial bound from prime divisibility and a finite binomial row. -/
theorem primorial_lt_four_pow_native (n : ℕ) (hn : n ≠ 0) :
    primorial n < 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ k =>
      rcases k.even_or_odd with ⟨m, rfl⟩ | hkodd
      · by_cases hm0 : m = 0
        · subst m
          decide
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hprior : primorial (m + 1) < 4 ^ (m + 1) :=
            ih (m + 1) (by omega) (by omega)
          have hsplit : primorial ((m + 1) + m) ≤
              primorial (m + 1) * Nat.choose ((m + 1) + m) (m + 1) :=
            interval_prime_product_bound (by omega)
          have hindex : (m + 1) + m = 2 * m + 1 := by omega
          rw [Nat.choose_symm_add, hindex] at hsplit
          have hmiddle : Nat.choose (2 * m + 1) m ≤ 4 ^ m :=
            odd_middle_bound m
          have hproduct : primorial (2 * m + 1) <
              4 ^ (m + 1) * 4 ^ m :=
            lt_of_le_of_lt hsplit
              (Nat.mul_lt_mul_of_lt_of_le hprior hmiddle (by simp))
          have hpow : 4 ^ (m + 1) * 4 ^ m = 4 ^ (2 * m + 1) := by
            rw [← pow_add]
            congr 1 <;> omega
          rw [hpow] at hproduct
          simpa only [two_mul, Nat.succ_eq_add_one] using hproduct
      · by_cases hk1 : k = 1
        · subst k
          decide
        · have hk0 : k ≠ 0 := by
            intro h
            subst k
            simp at hkodd
          have hprior : primorial k < 4 ^ k :=
            ih k (Nat.lt_succ_self k) hk0
          have heq : primorial (k + 1) = primorial k := by
            refine prod_congr ?_ fun _ _ => rfl
            rw [range_add_one, filter_insert, ite_eq_right fun h => not_even_iff_odd.2 hkodd _]
            exact fun h => h.even_sub_one <| mt Nat.succ.inj hk1
          have hpow : 4 ^ k ≤ 4 ^ (k + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
          simpa only [Nat.succ_eq_add_one, heq] using lt_of_lt_of_le hprior hpow

theorem primorial_le_four_pow_native (n : ℕ) : primorial n ≤ 4 ^ n := by
  by_cases hn : n = 0
  · subst n
    decide
  · exact (primorial_lt_four_pow_native n hn).le

/-- Exact theta upper bound from the finite prime product. -/
theorem theta_le_log4_mul_x_native {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ Real.log 4 * x := by
  have htheta : Chebyshev.theta x = Real.log (primorial ⌊x⌋₊ : ℝ) := by
    unfold Chebyshev.theta primorial
    rw [Nat.cast_prod, Real.log_prod (fun p hp => mod_cast (mem_filter.mp hp).2.pos.ne')]
    congr 1 with p
    simp_all [Nat.Prime.pos]
  rw [htheta]
  calc
    Real.log (primorial ⌊x⌋₊ : ℝ) ≤ Real.log ((4 : ℝ) ^ ⌊x⌋₊) := by
      apply Real.log_le_log
      · have hp : 0 < primorial ⌊x⌋₊ :=
          prod_pos (fun _ h => (mem_filter.1 h).2.pos)
        exact_mod_cast hp
      · exact_mod_cast primorial_le_four_pow_native ⌊x⌋₊
    _ = Real.log 4 * (⌊x⌋₊ : ℝ) := by rw [Real.log_pow]; ring
    _ ≤ Real.log 4 * x := by
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hx) (Real.log_nonneg (by norm_num))

end HVRNativeChebyshevBound
