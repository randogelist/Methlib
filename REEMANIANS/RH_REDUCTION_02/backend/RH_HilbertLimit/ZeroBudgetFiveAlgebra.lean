import RH_HilbertLimit.Geometry
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# Six-factor positivity in a rational complex sector

This module is purely algebraic. A complex number in the sector
`4 * |im| ≤ re` has argument at most arctan(1/4), but no argument function
or trigonometric theorem is used here. Exact rational cone multiplication
proves nonnegative real parts of products of at most six such factors.

Applied to `z` and `1-z`, this supplies every degree-at-most-five Bernstein
kernel with its additional spectral mass factor. It is a finite-degree
lemma and asserts neither all-order positivity nor RH.

Source preparation only; no Lean compiler or axiom audit was run here.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

private def zeroBudgetFiveCone (s : ℝ) (z : ℂ) : Prop :=
  0 ≤ z.re ∧ |z.im| ≤ s * z.re

/-- Multiplication of two rationally bounded cones, while their combined
angle is strictly below a right angle. -/
private theorem zeroBudgetFiveCone_mul {s t : ℝ} {z w : ℂ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hden : 0 < 1 - s * t)
    (hz : zeroBudgetFiveCone s z) (hw : zeroBudgetFiveCone t w) :
    zeroBudgetFiveCone ((s + t) / (1 - s * t)) (z * w) := by
  have hprod : |z.im| * |w.im| ≤ s * t * (z.re * w.re) := by
    calc
      |z.im| * |w.im| ≤ (s * z.re) * (t * w.re) :=
        mul_le_mul hz.2 hw.2 (abs_nonneg _) (mul_nonneg hs hz.1)
      _ = s * t * (z.re * w.re) := by ring
  have hcross : z.im * w.im ≤ |z.im| * |w.im| := by
    simpa only [abs_mul] using le_abs_self (z.im * w.im)
  have hreal : (1 - s * t) * (z.re * w.re) ≤ (z * w).re := by
    rw [Complex.mul_re]
    nlinarith only [hprod, hcross]
  have himag : |(z * w).im| ≤ (s + t) * (z.re * w.re) := by
    rw [Complex.mul_im]
    calc
      |z.re * w.im + z.im * w.re| ≤
          |z.re * w.im| + |z.im * w.re| := by
        apply abs_le.mpr
        constructor
        · linarith only [
            neg_le_abs (z.re * w.im),
            neg_le_abs (z.im * w.re)]
        · linarith only [
            le_abs_self (z.re * w.im),
            le_abs_self (z.im * w.re)]
      _ = z.re * |w.im| + |z.im| * w.re := by
        rw [abs_mul, abs_mul, abs_of_nonneg hz.1, abs_of_nonneg hw.1]
      _ ≤ z.re * (t * w.re) + (s * z.re) * w.re :=
        add_le_add (mul_le_mul_of_nonneg_left hw.2 hz.1)
          (mul_le_mul_of_nonneg_right hz.2 hw.1)
      _ = (s + t) * (z.re * w.re) := by ring
  have hscaledImag := mul_le_mul_of_nonneg_left himag hden.le
  have hscaledReal := mul_le_mul_of_nonneg_left hreal (add_nonneg hs ht)
  have hbound : (1 - s * t) * |(z * w).im| ≤ (s + t) * (z * w).re := by
    nlinarith only [hscaledImag, hscaledReal]
  constructor
  · exact (mul_nonneg hden.le (mul_nonneg hz.1 hw.1)).trans hreal
  · calc
      |(z * w).im| ≤ ((s + t) * (z * w).re) / (1 - s * t) := by
        apply (le_div_iff₀ hden).2
        nlinarith only [hbound]
      _ = ((s + t) / (1 - s * t)) * (z * w).re := by ring

/-- These are the exact slopes of `(4 + I)^n` through the sixth power. -/
private def zeroBudgetFiveSlope : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 8 / 15
  | 3 => 47 / 52
  | 4 => 240 / 161
  | 5 => 1121 / 404
  | _ => 4888 / 495

private theorem zeroBudgetFiveSlope_nonneg (n : ℕ) (hn : n ≤ 6) :
    0 ≤ zeroBudgetFiveSlope n := by
  interval_cases n <;> norm_num [zeroBudgetFiveSlope]

private theorem zeroBudgetFiveSlope_den_pos (n : ℕ) (hn : n < 6) :
    0 < 1 - zeroBudgetFiveSlope n * (1 / 4 : ℝ) := by
  interval_cases n <;> norm_num [zeroBudgetFiveSlope]

private theorem zeroBudgetFiveSlope_step (n : ℕ) (hn : n < 6) :
    zeroBudgetFiveSlope (n + 1) =
      (zeroBudgetFiveSlope n + (1 / 4 : ℝ)) /
        (1 - zeroBudgetFiveSlope n * (1 / 4 : ℝ)) := by
  interval_cases n <;> norm_num [zeroBudgetFiveSlope]

private theorem zeroBudgetFiveCone_step (n : ℕ) (hn : n < 6) {z w : ℂ}
    (hz : zeroBudgetFiveCone (zeroBudgetFiveSlope n) z)
    (hw : zeroBudgetFiveCone (1 / 4) w) :
    zeroBudgetFiveCone (zeroBudgetFiveSlope (n + 1)) (z * w) := by
  rw [zeroBudgetFiveSlope_step n hn]
  exact zeroBudgetFiveCone_mul (zeroBudgetFiveSlope_nonneg n (by omega))
    (by norm_num) (zeroBudgetFiveSlope_den_pos n hn) hz hw

/-- A product of at most six factors selected from two quarter-sector
numbers has nonnegative real part. -/
private theorem zeroBudgetFiveCone_powers (z w : ℂ)
    (hz : zeroBudgetFiveCone (1 / 4) z)
    (hw : zeroBudgetFiveCone (1 / 4) w) :
    ∀ n : ℕ, n ≤ 6 → ∀ a b : ℕ, a + b = n →
      zeroBudgetFiveCone (zeroBudgetFiveSlope n) (z ^ a * w ^ b) := by
  intro n
  induction n with
  | zero =>
      intro _hn a b hab
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      norm_num [zeroBudgetFiveCone, zeroBudgetFiveSlope]
  | succ n ih =>
      intro hn a b hab
      have hnlt : n < 6 := by omega
      by_cases ha : a = 0
      · subst a
        have hb : b = n + 1 := by omega
        subst b
        have hp := ih (by omega) 0 n (by omega)
        have hm := zeroBudgetFiveCone_step n hnlt hp hw
        simpa only [Nat.succ_eq_add_one, pow_zero, one_mul, pow_succ] using hm
      · obtain ⟨a', ha'⟩ := Nat.exists_eq_succ_of_ne_zero ha
        subst a
        have hp := ih (by omega) a' b (by omega)
        have hm := zeroBudgetFiveCone_step n hnlt hp hz
        simpa only [Nat.succ_eq_add_one, pow_succ, mul_assoc, mul_comm,
          mul_left_comm] using hm

/-- The exact finite-degree kernel sign used by the first five cancellation
checks. The two displayed wedge premises are numerical sector bounds. -/
theorem zeroBudget_re_pow_mul_one_sub_nonneg (z : ℂ) (a b : ℕ)
    (hdegree : a + b ≤ 6)
    (hz : 4 * |z.im| ≤ z.re)
    (hc : 4 * |z.im| ≤ 1 - z.re) :
    0 ≤ (z ^ a * (1 - z) ^ b).re := by
  have hzcone : zeroBudgetFiveCone (1 / 4) z := by
    constructor
    · linarith [abs_nonneg z.im]
    · linarith
  have hwcone : zeroBudgetFiveCone (1 / 4) (1 - z) := by
    constructor
    · simp only [Complex.sub_re, Complex.one_re]
      linarith [abs_nonneg z.im]
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.one_re]
      linarith
  exact (zeroBudgetFiveCone_powers z (1 - z) hzcone hwcone
    (a + b) hdegree a b rfl).1

end RH_HilbertLimit
