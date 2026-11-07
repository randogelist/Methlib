import RH_HilbertLimit.ZeroBudgetSecondSector

/-!
# Independent second cancellation test for the explicit budget `(0,0)`

The canonical nodes have positive real parts and unit complex total mass.
Their sector puts each node in the wedge `|im| ≤ re`; summing the two
nonnegative functions `re + im` and `re - im` gives the complementary wedge
`|im| ≤ 1 - re`. These bounds prove the two upper inequalities for moment
two. The stronger zero-free sector supplies positivity of the cubic sum.

Only cancellation indices zero and one are established. No universal
propagation, admissibility, finite accepted witness, or RH is asserted.
Source preparation only: native Windows compilation and audit are pending.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster

/-- A sector in the right half-plane controls the difference of powers two
and three. The hypotheses are pointwise numerical bounds, not RH. -/
theorem zeroBudget_cube_re_le_square_re_of_wedge (z : ℂ)
    (hre0 : 0 ≤ z.re) (hre1 : z.re ≤ 1)
    (him : z.im ^ 2 ≤ z.re ^ 2) :
    (z ^ 3).re ≤ (z ^ 2).re := by
  have h2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_succ, pow_zero, mul_one, one_mul, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im]
  have h3 : (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 := by
    simp only [pow_succ, pow_zero, mul_one, one_mul, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [h2, h3]
  by_cases ha : 1 ≤ 3 * z.re
  · have hp := mul_nonneg (sq_nonneg z.re) (sub_nonneg.mpr hre1)
    have hq := mul_nonneg (sq_nonneg z.im) (sub_nonneg.mpr ha)
    nlinarith
  · have hp := mul_nonneg (sub_nonneg.mpr him)
      (by linarith : 0 ≤ 1 - 3 * z.re)
    have hcube : 0 ≤ z.re ^ 3 := pow_nonneg hre0 3
    nlinarith

/-- The complementary wedge controls the degree-two left Bernstein weight. -/
theorem zeroBudget_twice_square_re_le_re_add_cube_re_of_wedge (z : ℂ)
    (hre0 : 0 ≤ z.re) (hre1 : z.re ≤ 1)
    (him : z.im ^ 2 ≤ (1 - z.re) ^ 2) :
    2 * (z ^ 2).re ≤ z.re + (z ^ 3).re := by
  have h2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_succ, pow_zero, mul_one, one_mul, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im]
  have h3 : (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 := by
    simp only [pow_succ, pow_zero, mul_one, one_mul, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [h2, h3]
  by_cases ha : 3 * z.re ≤ 2
  · have hp := mul_nonneg hre0 (sq_nonneg (1 - z.re))
    have hq := mul_nonneg (sq_nonneg z.im) (sub_nonneg.mpr ha)
    nlinarith
  · have hp := mul_nonneg (sub_nonneg.mpr him)
      (by linarith : 0 ≤ 3 * z.re - 2)
    have hcube : 0 ≤ (1 - z.re) ^ 3 :=
      pow_nonneg (sub_nonneg.mpr hre1) 3
    nlinarith

/-- The previously audited square positivity gives the first mass wedge. -/
theorem zeroBudget_canonicalNode_abs_im_le_re (i : ActualPairIndex) :
    |(canonicalNode i).im| ≤ (canonicalNode i).re := by
  have hre := zeroBudget_canonicalNode_re_pos i
  have hsquare := zeroBudget_canonicalNode_square_re_pos i
  simp only [pow_two, Complex.mul_re] at hsquare
  by_contra hn
  have hlt : (canonicalNode i).re < |(canonicalNode i).im| := lt_of_not_ge hn
  have hmul := mul_self_le_mul_self hre.le hlt.le
  nlinarith [sq_abs (canonicalNode i).im]

/-- Unit complex mass bounds each node in the complementary mass wedge. -/
theorem zeroBudget_canonicalNode_abs_im_le_one_sub_re (i : ActualPairIndex) :
    |(canonicalNode i).im| ≤ 1 - (canonicalNode i).re := by
  have hr : HasSum (fun j : ActualPairIndex => (canonicalNode j).re) 1 := by
    simpa using Complex.hasSum_re canonicalNode_mass_one
  have hi : HasSum (fun j : ActualPairIndex => (canonicalNode j).im) 0 := by
    simpa using Complex.hasSum_im canonicalNode_mass_one
  have hp : HasSum
      (fun j : ActualPairIndex => (canonicalNode j).re + (canonicalNode j).im) 1 := by
    simpa using hr.add hi
  have hm : HasSum
      (fun j : ActualPairIndex => (canonicalNode j).re - (canonicalNode j).im) 1 := by
    simpa using hr.sub hi
  have hplus := hp.summable.le_tsum i (fun j _ => by
    have h := (abs_le.mp (zeroBudget_canonicalNode_abs_im_le_re j)).1
    linarith)
  have hminus := hm.summable.le_tsum i (fun j _ => by
    have h := (abs_le.mp (zeroBudget_canonicalNode_abs_im_le_re j)).2
    linarith)
  rw [hp.tsum_eq] at hplus
  rw [hm.tsum_eq] at hminus
  apply abs_le.mpr
  constructor <;> linarith

/-- The second normalized moment is bounded by the first without RH. -/
theorem actualNormalizedMoment_two_le_one_moment :
    actualNormalizedMoment 2 ≤ actualNormalizedMoment 1 := by
  have hs2 : HasSum (fun i : ActualPairIndex => (canonicalNode i ^ 3).re)
      (actualNormalizedMoment 2) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 2)
  have hs1 : HasSum (fun i : ActualPairIndex => (canonicalNode i ^ 2).re)
      (actualNormalizedMoment 1) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 1)
  apply hasSum_le _ hs2 hs1
  intro i
  apply zeroBudget_cube_re_le_square_re_of_wedge (canonicalNode i)
    (zeroBudget_canonicalNode_re_pos i).le (zeroBudget_canonicalNode_re_le_one i)
  have h := mul_self_le_mul_self (abs_nonneg (canonicalNode i).im)
    (zeroBudget_canonicalNode_abs_im_le_re i)
  nlinarith [sq_abs (canonicalNode i).im]

/-- The left degree-two Bernstein weight is nonnegative without RH. -/
theorem actualNormalizedMoment_two_left_bound :
    2 * actualNormalizedMoment 1 ≤ 1 + actualNormalizedMoment 2 := by
  have hs2 : HasSum (fun i : ActualPairIndex => (canonicalNode i ^ 3).re)
      (actualNormalizedMoment 2) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 2)
  have hs1 : HasSum (fun i : ActualPairIndex => (canonicalNode i ^ 2).re)
      (actualNormalizedMoment 1) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 1)
  have hr : HasSum (fun i : ActualPairIndex => (canonicalNode i).re) 1 := by
    simpa using Complex.hasSum_re canonicalNode_mass_one
  apply hasSum_le _ (hs1.mul_left 2) (hr.add hs2)
  intro i
  apply zeroBudget_twice_square_re_le_re_add_cube_re_of_wedge (canonicalNode i)
    (zeroBudget_canonicalNode_re_pos i).le (zeroBudget_canonicalNode_re_le_one i)
  have h := mul_self_le_mul_self (abs_nonneg (canonicalNode i).im)
    (zeroBudget_canonicalNode_abs_im_le_one_sub_re i)
  nlinarith [sq_abs (canonicalNode i).im]

/-- The stronger unconditional zero-free sector makes the cubic power sum
strictly positive. -/
theorem actualNormalizedMoment_two_pos : 0 < actualNormalizedMoment 2 := by
  classical
  have hs : HasSum (fun i : ActualPairIndex => (canonicalNode i ^ 3).re)
      (actualNormalizedMoment 2) := by
    simpa using Complex.hasSum_re (canonicalPowerSums 2)
  obtain ⟨i⟩ := actualPairIndex_nonempty
  have hi := hs.summable.le_tsum i
    (fun j _ => (zeroBudget_canonicalNode_cube_re_pos j).le)
  rw [hs.tsum_eq] at hi
  exact lt_of_lt_of_le (zeroBudget_canonicalNode_cube_re_pos i) hi

theorem actualNormalizedMoment_two_nonneg : 0 ≤ actualNormalizedMoment 2 :=
  actualNormalizedMoment_two_pos.le

/-- The degree-two row has variation one, with no RH hypothesis. -/
theorem actualVariation_two_eq_one_unconditional : actualVariation 2 = 1 := by
  exact actualVariation_two_eq_one_iff.mpr
    ⟨actualNormalizedMoment_two_nonneg, actualNormalizedMoment_two_le_one_moment,
      actualNormalizedMoment_two_left_bound⟩

/-- The second cancellation check of the explicit zero budget. -/
theorem actual_rowCancellation_one_eq_zero_unconditional :
    rowCancellation actualNormalizedMoment 1 = 0 := by
  exact actual_rowCancellation_one_eq_zero_iff_unconditional.mpr
    ⟨actualNormalizedMoment_two_nonneg, actualNormalizedMoment_two_le_one_moment,
      actualNormalizedMoment_two_left_bound⟩

/-- This finite prefix is limited to cancellation indices zero and one. -/
theorem zeroBudgetCandidate_first_two_cancellations (n : ℕ) (hn : n < 2) :
    rowCancellation actualNormalizedMoment n = 0 := by
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl
  · exact actual_rowCancellation_zero_eq_zero_unconditional
  · exact actual_rowCancellation_one_eq_zero_unconditional

end RH_HilbertLimit
