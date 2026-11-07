import RH_HilbertLimit.ZeroBudgetTenKappa
import RH_HilbertLimit.ZeroBudgetFiveSector

/-!
# A seven-cone from the actual trace and conjugate zero pairing

Only the new scalar upper bound on actualKappa is imported. A nonreal
canonical scale has a distinct conjugate scale, so its two reciprocal real
parts are bounded by the complete positive trace. Together with the actual
critical strip and the frozen height 17/4 exclusion, this yields the cone
7 * |im| <= re. Real scales satisfy that cone directly.

Source candidate only: no Lean compiler, native runner, or CI was executed.
This finite-angle estimate does not assert RH or all-order admissibility.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate

namespace RH_HilbertLimit

open AngularMaster OverflowResidueRH

/-- The strip and frozen height estimate give two elementary scale bounds. -/
theorem zeroBudget_actualComplexScale_strip_square_bounds (i : ActualPairIndex) :
    (285 / 16 : ℝ) < (actualComplexScale i).re ∧
      (actualComplexScale i).im ^ 2 ≤ (actualComplexScale i).re + 1 / 4 := by
  let w : ℂ := Complex.sqrt (-actualComplexScale i)
  have hsq : w ^ 2 = -actualComplexScale i :=
    AWPIRH.complex_sqrt_sq (-actualComplexScale i)
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 :=
    actual_theta_neg_complexScale_zero i
  have hstrip := xi_zero_mem_critical_strip hxi
  have hheight := zeroBudget_xi_zero_17_4_lt_abs_im hxi
  have hwre : |w.re| < (1 / 2 : ℝ) := by
    apply abs_lt.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : (17 / 4 : ℝ) < |w.im| := by simpa using hheight
  have hreal : (actualComplexScale i).re = w.im ^ 2 - w.re ^ 2 := by
    have h := congrArg Complex.re hsq
    simp only [pow_two, Complex.mul_re, Complex.neg_re] at h
    nlinarith
  have himag : (actualComplexScale i).im = -(2 * w.re * w.im) := by
    have h := congrArg Complex.im hsq
    simp only [pow_two, Complex.mul_im, Complex.neg_im] at h
    linarith
  have hu : w.re ^ 2 < (1 / 4 : ℝ) := by
    have ha := (abs_lt.mp hwre).1
    have hb := (abs_lt.mp hwre).2
    have hp := mul_pos (sub_pos.mpr hb)
      (show 0 < (1 / 2 : ℝ) + w.re by linarith)
    nlinarith
  have hv : (289 / 16 : ℝ) < w.im ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hwim)
      (show 0 < |w.im| + (17 / 4 : ℝ) by positivity)
    nlinarith [sq_abs w.im]
  constructor
  · rw [hreal]
    linarith
  · rw [hreal, himag]
    have hp := mul_nonneg
      (show 0 ≤ 1 - 4 * w.re ^ 2 by linarith) (sq_nonneg w.im)
    nlinarith [sq_nonneg w.re, sq_nonneg w.im]

/-- A nonreal actual scale has a distinct conjugate occurrence. -/
theorem zeroBudget_actualComplexScale_conjugate_occurrence (i : ActualPairIndex)
    (him : (actualComplexScale i).im ≠ 0) :
    ∃ j : ActualPairIndex, j ≠ i ∧ actualComplexScale j = conj (actualComplexScale i) := by
  have hzero := actual_theta_neg_complexScale_zero i
  have hconj : AWPIRH.theta (conj (-actualComplexScale i)) = 0 := by
    rw [actual_theta_conj, hzero, map_zero]
  obtain ⟨j, hj⟩ := actualTheta_zero_has_canonical_scale hconj
  have hscale : actualComplexScale j = conj (actualComplexScale i) := by
    have h := congrArg (fun z : ℂ => -z) hj
    simpa only [map_neg, neg_neg] using h.symm
  refine ⟨j, ?_, hscale⟩
  intro hji
  have h := congrArg Complex.im hscale
  rw [hji] at h
  simp only [Complex.conj_im] at h
  apply him
  linarith

/-- Both conjugate reciprocal real parts occur in the positive actual trace. -/
theorem zeroBudget_actualInverseScale_double_re_le_kappa (i : ActualPairIndex)
    (him : (actualComplexScale i).im ≠ 0) :
    2 * ((actualComplexScale i)⁻¹).re ≤ actualKappa := by
  classical
  obtain ⟨j, hji, hscale⟩ :=
    zeroBudget_actualComplexScale_conjugate_occurrence i him
  have hij : i ≠ j := Ne.symm hji
  have hre : ((actualComplexScale j)⁻¹).re =
      ((actualComplexScale i)⁻¹).re := by
    rw [hscale, Complex.inv_re, Complex.inv_re]
    simp only [Complex.conj_re, Complex.normSq_conj]
  have hmass := actualComplexScale_inv_re_summable.sum_le_tsum
    ({i, j} : Finset ActualPairIndex) (fun k _ => (actualInverseScale_re_pos k).le)
  have hmass' : ((actualComplexScale i)⁻¹).re +
      ((actualComplexScale j)⁻¹).re ≤ actualKappa := by
    simpa only [Finset.sum_pair hij, ← actualKappa_eq_canonical_trace] using hmass
  rw [hre] at hmass'
  linarith

/-- The new scalar kappa bound constrains every nonreal scale quantitatively. -/
theorem zeroBudget_actualComplexScale_trace_quadratic (i : ActualPairIndex)
    (him : (actualComplexScale i).im ≠ 0) :
    207 * (actualComplexScale i).re ≤
      4 * ((actualComplexScale i).re ^ 2 + (actualComplexScale i).im ^ 2) := by
  have hd : 0 < Complex.normSq (actualComplexScale i) :=
    Complex.normSq_pos.mpr (actualComplexScale_ne_zero i)
  have hle := (zeroBudget_actualInverseScale_double_re_le_kappa i him).trans
    zeroBudget_actualKappa_le_eight_207
  rw [Complex.inv_re] at hle
  have hratio : (2 * (actualComplexScale i).re) /
      Complex.normSq (actualComplexScale i) ≤ (8 / 207 : ℝ) := by
    simpa only [mul_div_assoc] using hle
  have hm := (div_le_iff₀ hd).mp hratio
  simp only [Complex.normSq_apply] at hm
  nlinarith

/-- The stronger cone is forced by the paired trace, not by an RH assumption. -/
theorem zeroBudget_actualComplexScale_seven_abs_im_le_re (i : ActualPairIndex) :
    7 * |(actualComplexScale i).im| ≤ (actualComplexScale i).re := by
  obtain ⟨hlower, hstrip⟩ := zeroBudget_actualComplexScale_strip_square_bounds i
  by_cases him : (actualComplexScale i).im = 0
  · rw [him, abs_zero, mul_zero]
    linarith
  have htrace := zeroBudget_actualComplexScale_trace_quadratic i him
  by_contra hn
  have hbad : (actualComplexScale i).re < 7 * |(actualComplexScale i).im| :=
    lt_of_not_ge hn
  have hsq := mul_self_le_mul_self
    (show 0 ≤ (actualComplexScale i).re by linarith) hbad.le
  nlinarith [sq_abs (actualComplexScale i).im]

/-- Reciprocal scaling preserves the seven-cone for the literal actual nodes. -/
theorem zeroBudget_canonicalNode_seven_abs_im_le_re (i : ActualPairIndex) :
    7 * |(canonicalNode i).im| ≤ (canonicalNode i).re := by
  have hd : 0 < Complex.normSq (actualComplexScale i) :=
    Complex.normSq_pos.mpr (actualComplexScale_ne_zero i)
  have hinv : 7 * |((actualComplexScale i)⁻¹).im| ≤
      ((actualComplexScale i)⁻¹).re := by
    rw [Complex.inv_im, Complex.inv_re, abs_div, abs_neg, abs_of_pos hd,
      ← mul_div_assoc]
    have h := mul_le_mul_of_nonneg_right
      (zeroBudget_actualComplexScale_seven_abs_im_le_re i) (inv_pos.mpr hd).le
    simpa only [div_eq_mul_inv] using h
  rw [canonicalNode_eq_inverseScale_mul]
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  rw [abs_mul, abs_of_pos (inv_pos.mpr actualKappa_pos)]
  nlinarith [mul_le_mul_of_nonneg_left hinv (inv_pos.mpr actualKappa_pos).le]

end RH_HilbertLimit
