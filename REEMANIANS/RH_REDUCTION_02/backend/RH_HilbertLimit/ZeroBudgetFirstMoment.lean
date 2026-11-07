import RH_HilbertLimit.ZeroBudgetCandidate

/-!
# Independent first cancellation test for the explicit budget `(0,0)`

The existing literal theta-kernel bound excludes xi zeros up to height 5/4.
That quantitative improvement makes the real part of every squared canonical
node positive. The exact canonical power sums and unit mass then prove
`0 < actualNormalizedMoment 1` and `actualNormalizedMoment 1 ≤ 1`.
Consequently the first actual cancellation row is zero, without assuming RH.

This proves only the first cancellation row, not the universal admissibility
of the zero budget. No finite complete checker or accepted RH witness is
claimed. Prepared by source inspection only; native compilation is pending.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster

/-- A concrete strip bound extending the existing height-one arithmetic. -/
theorem zeroBudget_norm_mul_sub_one_le_41_16 {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ (5 / 4 : ℝ)) :
    ‖s * (s - 1)‖ ≤ (41 / 16 : ℝ) := by
  have him : s.im ^ 2 ≤ (25 / 16 : ℝ) := by
    have h := mul_self_le_mul_self (abs_nonneg s.im) ht
    nlinarith [sq_abs s.im]
  have hre : s.re ^ 2 ≤ 1 := by nlinarith
  have hre' : (s.re - 1) ^ 2 ≤ 1 := by nlinarith
  have hn : ‖s‖ ^ 2 ≤ (41 / 16 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hn' : ‖s - 1‖ ^ 2 ≤ (41 / 16 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero]
    nlinarith
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

/-- The archived theta-kernel estimate alone excludes height at most 5/4. -/
theorem zeroBudget_xi_ne_zero_of_abs_im_le_five_fourths {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ (5 / 4 : ℝ)) :
    AWPIRH.xi s ≠ 0 := by
  intro hz
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤
      (123 / 128 : ℝ) := by
    rw [norm_mul]
    calc
      ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤
          (41 / 16 : ℝ) * (3 / 8 : ℝ) :=
        mul_le_mul (zeroBudget_norm_mul_sub_one_le_41_16 hs0 hs1 ht)
          (actual_completedZeta₀_norm_le_three_eighths hs0 hs1)
          (norm_nonneg _) (by norm_num)
      _ = (123 / 128 : ℝ) := by norm_num
  linarith

/-- This lower zero-height bound is unconditional and uses no computed zeros. -/
theorem zeroBudget_xi_zero_five_fourths_lt_abs_im {s : ℂ}
    (hz : AWPIRH.xi s = 0) : (5 / 4 : ℝ) < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  exact zeroBudget_xi_ne_zero_of_abs_im_le_five_fourths
    hs.1.le hs.2.le (le_of_not_gt hn) hz

/-- Squaring a centered zero gives the sector needed for the second power. -/
theorem zeroBudget_theta_zero_angle_le_neg_21_29 {z : ℂ}
    (hz0 : z ≠ 0) (hz : AWPIRH.theta z = 0) :
    z.re / ‖z‖ ≤ -(21 / 29 : ℝ) := by
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hw : w ≠ 0 := by
    intro h
    apply hz0
    rw [← hsq, h]
    simp
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hstrip := xi_zero_mem_critical_strip hxi
  have hbig := zeroBudget_xi_zero_five_fourths_lt_abs_im hxi
  have hwre : |w.re| < (1 / 2 : ℝ) := by
    apply abs_lt.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : (5 / 4 : ℝ) < |w.im| := by simpa using hbig
  have hangle := square_angle_le_cutoff_of_le_abs_im
    (by norm_num : (0 : ℝ) < 5 / 2) hw
    (by nlinarith : (5 / 2 : ℝ) * |w.re| ≤ |w.im|)
  norm_num [hsq, slopeCutoff] at hangle
  exact hangle

/-- The strengthened sector makes the square of each actual scale real-positive. -/
theorem zeroBudget_actualComplexScale_square_re_pos (i : ActualPairIndex) :
    0 < (actualComplexScale i ^ 2).re := by
  have hn : 0 < ‖actualComplexScale i‖ :=
    norm_pos_iff.mpr (actualComplexScale_ne_zero i)
  have hangle := zeroBudget_theta_zero_angle_le_neg_21_29
    (neg_ne_zero.mpr (actualComplexScale_ne_zero i))
    (actual_theta_neg_complexScale_zero i)
  simp only [Complex.neg_re, norm_neg] at hangle
  have hre : (21 / 29 : ℝ) * ‖actualComplexScale i‖ ≤
      (actualComplexScale i).re := by
    have h := (div_le_iff₀ hn).mp hangle
    linarith
  have hsq := mul_self_le_mul_self
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21 / 29) hn.le) hre
  have hnorm : (actualComplexScale i).re ^ 2 +
      (actualComplexScale i).im ^ 2 = ‖actualComplexScale i‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hn2 : 0 < ‖actualComplexScale i‖ ^ 2 := sq_pos_of_pos hn
  simp only [pow_two, Complex.mul_re]
  nlinarith

/-- Canonical node real parts are positive without an RH hypothesis. -/
theorem zeroBudget_canonicalNode_re_pos (i : ActualPairIndex) :
    0 < (canonicalNode i).re := by
  rw [canonicalNode_eq_inverseScale_mul]
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (inv_pos.mpr actualKappa_pos) (actualInverseScale_re_pos i)

/-- Positive canonical real masses have unit total mass. -/
theorem zeroBudget_canonicalNode_re_le_one (i : ActualPairIndex) :
    (canonicalNode i).re ≤ 1 := by
  have hs : HasSum (fun j : ActualPairIndex => (canonicalNode j).re) 1 := by
    simpa using Complex.hasSum_re canonicalNode_mass_one
  have h := hs.summable.le_tsum i
    (fun j _ => (zeroBudget_canonicalNode_re_pos j).le)
  simpa only [hs.tsum_eq] using h

/-- Every term of the literal second canonical power sum has positive real part. -/
theorem zeroBudget_canonicalNode_square_re_pos (i : ActualPairIndex) :
    0 < (canonicalNode i ^ 2).re := by
  have hinv : 0 < (((actualComplexScale i)⁻¹) ^ 2).re := by
    have heq : ((actualComplexScale i)⁻¹) ^ 2 =
        (actualComplexScale i ^ 2)⁻¹ := by simp only [inv_pow]
    rw [heq, Complex.inv_re]
    exact div_pos (zeroBudget_actualComplexScale_square_re_pos i)
      (Complex.normSq_pos.mpr (pow_ne_zero 2 (actualComplexScale_ne_zero i)))
  rw [canonicalNode_eq_inverseScale_mul, mul_pow]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr actualKappa_pos)) hinv

/-- The first nonconstant actual normalized moment is strictly positive. -/
theorem actualNormalizedMoment_one_pos : 0 < actualNormalizedMoment 1 := by
  classical
  have hs : HasSum
      (fun i : ActualPairIndex => (canonicalNode i ^ 2).re)
      (actualNormalizedMoment 1) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 1)
  obtain ⟨i⟩ := actualPairIndex_nonempty
  have hi := hs.summable.le_tsum i
    (fun j _ => (zeroBudget_canonicalNode_square_re_pos j).le)
  rw [hs.tsum_eq] at hi
  exact lt_of_lt_of_le (zeroBudget_canonicalNode_square_re_pos i) hi

theorem actualNormalizedMoment_one_nonneg : 0 ≤ actualNormalizedMoment 1 :=
  actualNormalizedMoment_one_pos.le

/-- Unit real mass bounds the first normalized moment above by one. -/
theorem actualNormalizedMoment_one_le_one : actualNormalizedMoment 1 ≤ 1 := by
  have hs : HasSum
      (fun i : ActualPairIndex => (canonicalNode i ^ 2).re)
      (actualNormalizedMoment 1) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 1)
  have hm : HasSum (fun i : ActualPairIndex => (canonicalNode i).re) 1 := by
    simpa using Complex.hasSum_re canonicalNode_mass_one
  apply hasSum_le _ hs hm
  intro i
  have hpos := (zeroBudget_canonicalNode_re_pos i).le
  have hle := zeroBudget_canonicalNode_re_le_one i
  have hprod := mul_nonneg hpos (sub_nonneg.mpr hle)
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (canonicalNode i).im]

/-- The first cancellation row of the explicit candidate is proved independently. -/
theorem actual_rowCancellation_zero_eq_zero_unconditional :
    rowCancellation actualNormalizedMoment 0 = 0 := by
  exact actual_rowCancellation_zero_eq_zero_iff.mpr
    ⟨actualNormalizedMoment_one_nonneg, actualNormalizedMoment_one_le_one⟩

/-- The first refinement has variation one without assuming RH. -/
theorem actualVariation_one_eq_one_unconditional : actualVariation 1 = 1 := by
  rw [actualVariation_one_eq]
  rw [abs_of_nonneg (sub_nonneg.mpr actualNormalizedMoment_one_le_one),
    abs_of_nonneg actualNormalizedMoment_one_nonneg]
  ring

/-- After the independent first check, these are the exact next obligations. -/
theorem actual_rowCancellation_one_eq_zero_iff_unconditional :
    rowCancellation actualNormalizedMoment 1 = 0 ↔
      0 ≤ actualNormalizedMoment 2 ∧
      actualNormalizedMoment 2 ≤ actualNormalizedMoment 1 ∧
      2 * actualNormalizedMoment 1 ≤ 1 + actualNormalizedMoment 2 := by
  exact actual_rowCancellation_one_eq_zero_iff
    ⟨actualNormalizedMoment_one_nonneg, actualNormalizedMoment_one_le_one⟩

/-- The seed is now proved; this universal propagation law remains open. -/
theorem zeroBudgetCandidate_admissible_iff_propagation :
    zeroBudgetCandidate.Admissible ↔
      ∀ n : ℕ, rowCancellation actualNormalizedMoment n = 0 →
        rowCancellation actualNormalizedMoment (n + 1) = 0 := by
  constructor
  · intro h
    exact (zeroBudgetCandidate_admissible_iff_seed_and_propagation.mp h).2
  · intro hstep
    exact zeroBudgetCandidate_admissible_iff_seed_and_propagation.mpr
      ⟨actual_rowCancellation_zero_eq_zero_unconditional, hstep⟩

end RH_HilbertLimit
