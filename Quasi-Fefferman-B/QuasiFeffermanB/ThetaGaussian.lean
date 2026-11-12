import Mathlib

/-! Concrete normalized one-dimensional Gaussian theta endpoints. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuasiFeffermanB
noncomputable section

/-- The normalized real Gaussian theta series. -/
def gaussianThetaOne (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)

theorem gaussianThetaOne_nonneg (t : ℝ) : 0 ≤ gaussianThetaOne t := by
  exact tsum_nonneg (fun n => (Real.exp_pos _).le)

theorem gaussianThetaOne_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero, mul_assoc] using
    summable_pow_mul_jacobiTheta₂_term_bound 0 ht 0

/-- Identification with the already formalized Jacobi theta function. -/
theorem gaussianThetaOne_jacobi (t : ℝ) :
    jacobiTheta (Complex.I * (t : ℂ)) = (gaussianThetaOne t : ℂ) := by
  unfold jacobiTheta gaussianThetaOne
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Exact one-dimensional Jacobi transformation with normalized parameter. -/
theorem GAUSSIAN_THETA_ONE_TRANSFORM (t : ℝ) (ht : 0 < t) :
    gaussianThetaOne t =
      (1 / t ^ (1 / 2 : ℝ)) * gaussianThetaOne (1 / t) := by
  unfold gaussianThetaOne
  convert Real.tsum_exp_neg_mul_int_sq ht using 1
  congr 1
  apply tsum_congr
  intro n
  congr 1
  ring

/-- The native Jacobi estimate gives the explicit geometric tail majorant. -/
theorem GAUSSIAN_THETA_ONE_GEOMETRIC_TAIL (t : ℝ) (ht : 0 < t) :
    gaussianThetaOne t - 1 ≤
      2 / (1 - Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * t) := by
  have him : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  have h := norm_jacobiTheta_sub_one_le him
  rw [gaussianThetaOne_jacobi] at h
  have habs : |gaussianThetaOne t - 1| ≤
      2 / (1 - Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * t) := by
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] using h
  exact (le_abs_self _).trans habs

/-- Rational certificate used in the theta tail estimate. -/
theorem SIXTEEN_LT_EXP_PI : (16 : ℝ) < Real.exp Real.pi := by
  have hexp3 : (131 / 8 : ℝ) ≤ Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 5
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    exact h
  have h3pi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hm := Real.exp_lt_exp.mpr h3pi
  linarith

theorem EXP_NEG_PI_LT_ONE_SIXTEENTH : Real.exp (-Real.pi) < 1 / 16 := by
  rw [Real.exp_neg]
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) SIXTEEN_LT_EXP_PI

/-- Exact rational anchor: the three-dimensional product theta at t=1 is
strictly below 2. The lattice product identification is a separate endpoint. -/
theorem GAUSSIAN_THETA_ONE_CUBE_AT_ONE_LT_TWO : gaussianThetaOne 1 ^ 3 < 2 := by
  have htail := GAUSSIAN_THETA_ONE_GEOMETRIC_TAIL 1 (by norm_num)
  simp only [mul_one] at htail
  have hq := EXP_NEG_PI_LT_ONE_SIXTEENTH
  have hq0 := (Real.exp_pos (-Real.pi)).le
  have hd : 0 < 1 - Real.exp (-Real.pi) := by linarith
  have hfrac : 2 / (1 - Real.exp (-Real.pi)) * Real.exp (-Real.pi) < 2 / 15 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).mpr
    linarith
  have htheta : gaussianThetaOne 1 < 17 / 15 := by linarith
  have hnonneg := gaussianThetaOne_nonneg 1
  have hcube := pow_lt_pow_left₀ htheta hnonneg (by norm_num : (3 : ℕ) ≠ 0)
  norm_num at hcube
  linarith

/-- Exponential decay dominates the exact normalized three-dimensional power
on the large-parameter half of the Jacobi reflection. -/
theorem GAUSSIAN_EXP_TAIL_LE_POWER (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (Real.pi * (1 - t)) ≤ t ^ (-3 / 2 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [Real.rpow_def_of_pos ht0]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_sub_one_of_pos ht0
  have hpi : (3 / 2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hpi (sub_nonneg.mpr ht)
  nlinarith

/-- Concrete cube-theta envelope for normalized parameter t≥1. -/
theorem GAUSSIAN_THETA_CUBE_LARGE (t : ℝ) (ht : 1 ≤ t) :
    gaussianThetaOne t ^ 3 - 1 ≤ t ^ (-3 / 2 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let q : ℝ := Real.exp (-Real.pi * t)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq : q ≤ 1 / 16 := by
    have harg : -Real.pi * t ≤ -Real.pi := by
      nlinarith [Real.pi_pos]
    exact (Real.exp_le_exp.mpr harg).trans EXP_NEG_PI_LT_ONE_SIXTEENTH.le
  have hd : 0 < 1 - q := by linarith
  have hratio : 2 / (1 - q) ≤ 32 / 15 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have htail := GAUSSIAN_THETA_ONE_GEOMETRIC_TAIL t ht0
  change gaussianThetaOne t - 1 ≤ 2 / (1 - q) * q at htail
  have htheta : gaussianThetaOne t ≤ 1 + (32 / 15) * q := by
    have hm := mul_le_mul_of_nonneg_right hratio hq0
    linarith
  have hcube := pow_le_pow_left₀ (gaussianThetaOne_nonneg t) htheta 3
  have hq2 : q ^ 2 ≤ q / 16 := by
    have hm := mul_le_mul_of_nonneg_left hq hq0
    nlinarith
  have hq3 : q ^ 3 ≤ q / 256 := by
    have hm := mul_le_mul_of_nonneg_left hq2 hq0
    nlinarith
  have hpoly : gaussianThetaOne t ^ 3 - 1 ≤ 16 * q := by
    nlinarith
  have hexp : 16 * q ≤ Real.exp (Real.pi * (1 - t)) := by
    calc
      16 * q ≤ Real.exp Real.pi * q :=
        mul_le_mul_of_nonneg_right SIXTEEN_LT_EXP_PI.le hq0
      _ = Real.exp (Real.pi * (1 - t)) := by
        dsimp [q]
        rw [← Real.exp_add]
        congr 1
        ring
  exact hpoly.trans (hexp.trans (GAUSSIAN_EXP_TAIL_LE_POWER t ht))

/-- Exact three-dimensional product envelope, including the small-parameter
range obtained from the Jacobi reflection. -/
theorem GAUSSIAN_THETA_CUBE_ENVELOPE (t : ℝ) (ht : 0 < t) :
    gaussianThetaOne t ^ 3 - 1 ≤ t ^ (-3 / 2 : ℝ) := by
  by_cases ht1 : 1 ≤ t
  · exact GAUSSIAN_THETA_CUBE_LARGE t ht1
  have hsmall : t ≤ 1 := (lt_of_not_ge ht1).le
  have hinv : 1 ≤ 1 / t := (le_div_iff₀ ht).mpr (by simpa using hsmall)
  have hlarge := GAUSSIAN_THETA_CUBE_LARGE (1 / t) hinv
  have hreflect : gaussianThetaOne t ^ 3 =
      t ^ (-3 / 2 : ℝ) * gaussianThetaOne (1 / t) ^ 3 := by
    rw [GAUSSIAN_THETA_ONE_TRANSFORM t ht, mul_pow, div_pow, one_pow,
      ← Real.rpow_mul_natCast ht.le]
    have hexp : (1 / 2 : ℝ) * (3 : ℕ) = 3 / 2 := by norm_num
    rw [hexp]
    congr 1
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring, Real.rpow_neg ht.le]
    exact one_div _
  have hprod : t ^ (-3 / 2 : ℝ) * (1 / t) ^ (-3 / 2 : ℝ) = 1 := by
    rw [← Real.mul_rpow ht.le (one_div_nonneg.mpr ht.le), mul_one_div_cancel ht.ne',
      Real.one_rpow]
  have hmul := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg ht.le (-3 / 2 : ℝ))
  rw [mul_sub, mul_one, hprod, ← hreflect] at hmul
  linarith

end
end QuasiFeffermanB
