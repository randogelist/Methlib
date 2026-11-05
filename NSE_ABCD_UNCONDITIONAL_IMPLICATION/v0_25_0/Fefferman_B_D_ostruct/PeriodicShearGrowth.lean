import Mathlib

namespace PeriodicShear

noncomputable section

/-- The exponentially weighted spatial Fourier power at frequency `k`. -/
def weightedPower (d k : ℕ) : ℝ :=
  (k : ℝ) ^ d * Real.exp (-(k : ℝ))

/-- Absolute value of the formal order-`m` time derivative at the origin,
with heat eigenvalues `a * k²`. Frequencies start at one. -/
def moment (a : ℝ) (m : ℕ) : ℝ :=
  a ^ m * ∑' k : ℕ, weightedPower (2 * m) (k + 1)

theorem exp_neg_nat_eq_pow (k : ℕ) :
    Real.exp (-(k : ℝ)) = (Real.exp (-1)) ^ k := by
  simpa only [mul_neg, mul_one] using Real.exp_nat_mul (-1) k

theorem weightedPower_nonneg (d k : ℕ) : 0 ≤ weightedPower d k := by
  unfold weightedPower
  positivity

theorem summable_weightedPower (d : ℕ) : Summable (weightedPower d) := by
  have hq : ‖Real.exp (-1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  apply (summable_pow_mul_geometric_of_norm_lt_one d hq).congr
  intro k
  change (k : ℝ) ^ d * Real.exp (-1) ^ k =
    (k : ℝ) ^ d * Real.exp (-(k : ℝ))
  exact congrArg (fun w : ℝ => (k : ℝ) ^ d * w) (exp_neg_nat_eq_pow k).symm

theorem summable_weightedPower_succ (d : ℕ) :
    Summable (fun k : ℕ => weightedPower d (k + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_weightedPower d)

theorem moment_mode_lower (a : ℝ) (ha : 0 ≤ a) (m k : ℕ) :
    a ^ m * weightedPower (2 * m) (k + 1) ≤ moment a m := by
  unfold moment
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha m)
  exact (summable_weightedPower_succ (2 * m)).le_tsum k
    (fun j _ => weightedPower_nonneg _ (j + 1))

/-- The single positive mode `k = m` already gives a lower bound growing
faster than any factorial-geometric sequence. -/
theorem moment_factorial_lower (a : ℝ) (ha : 0 ≤ a) (m : ℕ) (hm : m ≠ 0) :
    (a * Real.exp (-1) * (m : ℝ)) ^ m * (m.factorial : ℝ) ≤ moment a m := by
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hk := moment_mode_lower a ha m (m - 1)
  rw [show m - 1 + 1 = m by omega] at hk
  calc
    (a * Real.exp (-1) * (m : ℝ)) ^ m * (m.factorial : ℝ)
        ≤ (a * Real.exp (-1) * (m : ℝ)) ^ m * (m : ℝ) ^ m := by
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = a ^ m * weightedPower (2 * m) m := by
      simp only [weightedPower, exp_neg_nat_eq_pow, two_mul, pow_add, mul_pow]
      ring
    _ ≤ moment a m := hk

/-- No single Cauchy bound for the Fourier moments can hold at all orders. -/
theorem moment_no_factorial_bound (a : ℝ) (ha : 0 < a) :
    ¬ ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ m : ℕ,
      moment a m ≤ C * (m.factorial : ℝ) * R ^ m := by
  rintro ⟨C, R, hC, hR, hbound⟩
  let b : ℝ := a * Real.exp (-1)
  let L : ℝ := max 1 C + 1
  have hb : 0 < b := mul_pos ha (Real.exp_pos _)
  have hL : 1 ≤ L := by dsimp [L]; linarith [le_max_left (1 : ℝ) C]
  have hCL : C < L := by dsimp [L]; linarith [le_max_right (1 : ℝ) C]
  obtain ⟨m, hm⟩ := exists_nat_gt (L * R / b)
  have hLR : 0 < L * R := mul_pos (lt_of_lt_of_le zero_lt_one hL) hR
  have hbig : L * R < b * (m : ℝ) := by
    calc
      L * R < (m : ℝ) * b := (div_lt_iff₀ hb).mp hm
      _ = b * (m : ℝ) := mul_comm _ _
  have hmne : m ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, mul_zero] at hbig
    exact (not_lt_of_ge hLR.le) hbig
  have hmajor : C * R ^ m < (b * (m : ℝ)) ^ m := by
    calc
      C * R ^ m < L ^ m * R ^ m :=
        mul_lt_mul_of_pos_right (hCL.trans_le (le_self_pow₀ hL hmne)) (pow_pos hR _)
      _ = (L * R) ^ m := (mul_pow L R m).symm
      _ ≤ (b * (m : ℝ)) ^ m := pow_le_pow_left₀ hLR.le hbig.le _
  have hfac : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hstrict : C * (m.factorial : ℝ) * R ^ m <
      (b * (m : ℝ)) ^ m * (m.factorial : ℝ) := by
    calc
      C * (m.factorial : ℝ) * R ^ m = (C * R ^ m) * (m.factorial : ℝ) := by ring
      _ < _ := mul_lt_mul_of_pos_right hmajor hfac
  exact (not_lt_of_ge ((moment_factorial_lower a ha.le m hmne).trans (hbound m))) hstrict

end
end PeriodicShear
