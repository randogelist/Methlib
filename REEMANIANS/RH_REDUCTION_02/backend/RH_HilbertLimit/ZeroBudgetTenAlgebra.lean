import RH_HilbertLimit.Geometry
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# Eleven-factor positivity in a rational complex sector

This module is purely algebraic. Exact rational cone multiplication proves
nonnegative real parts of products of at most eleven factors satisfying
`7 * |im| ≤ re`. No argument function or trigonometric theorem is used.

Applied to `z` and `1-z`, this supplies every degree-at-most-ten Bernstein
kernel with its additional spectral mass factor. This is a finite-degree
lemma and asserts neither all-order positivity nor RH.

The generic multiplication and exponent-induction proof is adapted from the
user-passed v0.2.30 first-five module. The new sector and degree constants
were checked using exact rational arithmetic only. This new module has not
been compiled or axiom-audited by the assistant; native verification remains
required.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

private def zeroBudgetTenCone (s : ℝ) (z : ℂ) : Prop :=
  0 ≤ z.re ∧ |z.im| ≤ s * z.re

/-- Multiplication of two rationally bounded cones, while their combined
angle is strictly below a right angle. -/
private theorem zeroBudgetTenCone_mul {s t : ℝ} {z w : ℂ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hden : 0 < 1 - s * t)
    (hz : zeroBudgetTenCone s z) (hw : zeroBudgetTenCone t w) :
    zeroBudgetTenCone ((s + t) / (1 - s * t)) (z * w) := by
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

/-- These are the exact slopes of `(7 + I)^n` through the eleventh power. -/
private def zeroBudgetTenSlope : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 7
  | 2 => 7 / 24
  | 3 => 73 / 161
  | 4 => 336 / 527
  | 5 => 2879 / 3353
  | 6 => 11753 / 10296
  | 7 => 92567 / 60319
  | 8 => 354144 / 164833
  | 9 => 2643841 / 799687
  | 10 => 9653287 / 1476984
  | _ => 69049993 / 685601

private theorem zeroBudgetTenSlope_nonneg (n : ℕ) (hn : n ≤ 11) :
    0 ≤ zeroBudgetTenSlope n := by
  interval_cases n <;> norm_num [zeroBudgetTenSlope]

private theorem zeroBudgetTenSlope_den_pos (n : ℕ) (hn : n < 11) :
    0 < 1 - zeroBudgetTenSlope n * (1 / 7 : ℝ) := by
  interval_cases n <;> norm_num [zeroBudgetTenSlope]

private theorem zeroBudgetTenSlope_step (n : ℕ) (hn : n < 11) :
    zeroBudgetTenSlope (n + 1) =
      (zeroBudgetTenSlope n + (1 / 7 : ℝ)) /
        (1 - zeroBudgetTenSlope n * (1 / 7 : ℝ)) := by
  interval_cases n <;> norm_num [zeroBudgetTenSlope]

private theorem zeroBudgetTenCone_step (n : ℕ) (hn : n < 11) {z w : ℂ}
    (hz : zeroBudgetTenCone (zeroBudgetTenSlope n) z)
    (hw : zeroBudgetTenCone (1 / 7) w) :
    zeroBudgetTenCone (zeroBudgetTenSlope (n + 1)) (z * w) := by
  rw [zeroBudgetTenSlope_step n hn]
  exact zeroBudgetTenCone_mul (zeroBudgetTenSlope_nonneg n (by omega))
    (by norm_num) (zeroBudgetTenSlope_den_pos n hn) hz hw

/-- A product of at most eleven factors selected from two seventh-sector
numbers has nonnegative real part. -/
private theorem zeroBudgetTenCone_powers (z w : ℂ)
    (hz : zeroBudgetTenCone (1 / 7) z)
    (hw : zeroBudgetTenCone (1 / 7) w) :
    ∀ n : ℕ, n ≤ 11 → ∀ a b : ℕ, a + b = n →
      zeroBudgetTenCone (zeroBudgetTenSlope n) (z ^ a * w ^ b) := by
  intro n
  induction n with
  | zero =>
      intro _hn a b hab
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      norm_num [zeroBudgetTenCone, zeroBudgetTenSlope]
  | succ n ih =>
      intro hn a b hab
      have hnlt : n < 11 := by omega
      by_cases ha : a = 0
      · subst a
        have hb : b = n + 1 := by omega
        subst b
        have hp := ih (by omega) 0 n (by omega)
        have hm := zeroBudgetTenCone_step n hnlt hp hw
        simpa only [Nat.succ_eq_add_one, pow_zero, one_mul, pow_succ] using hm
      · obtain ⟨a', ha'⟩ := Nat.exists_eq_succ_of_ne_zero ha
        subst a
        have hp := ih (by omega) a' b (by omega)
        have hm := zeroBudgetTenCone_step n hnlt hp hz
        simpa only [Nat.succ_eq_add_one, pow_succ, mul_assoc, mul_comm,
          mul_left_comm] using hm

/-- The exact finite-degree kernel sign used by the first ten cancellation
checks. The two displayed wedge premises are numerical sector bounds. -/
theorem zeroBudgetTen_re_pow_mul_one_sub_nonneg (z : ℂ) (a b : ℕ)
    (hdegree : a + b ≤ 11)
    (hz : 7 * |z.im| ≤ z.re)
    (hc : 7 * |z.im| ≤ 1 - z.re) :
    0 ≤ (z ^ a * (1 - z) ^ b).re := by
  have hzcone : zeroBudgetTenCone (1 / 7) z := by
    constructor
    · linarith [abs_nonneg z.im]
    · linarith
  have hwcone : zeroBudgetTenCone (1 / 7) (1 - z) := by
    constructor
    · simp only [Complex.sub_re, Complex.one_re]
      linarith [abs_nonneg z.im]
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.one_re]
      linarith
  exact (zeroBudgetTenCone_powers z (1 - z) hzcone hwcone
    (a + b) hdegree a b rfl).1

end RH_HilbertLimit
