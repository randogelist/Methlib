import RH_HilbertLimit.ZeroBudgetFiveSector
import RH_HilbertLimit.ZeroBudgetFiveAlgebra

/-!
# First five cancellation indices for the explicit zero budget

The independent narrow sector and unit canonical mass give complementary
quarter-wedges for every actual node. The finite-degree algebra controls
products of at most six factors. Exact canonical spectral summation then
gives nonnegative Bernstein rows of degrees zero through five, and hence
zero cancellation at indices zero through four.

The degree restriction is essential. No assertion at cancellation indices
five through nine, universal propagation, full witness admissibility, or RH
is made. Prepared without executing Lean; native compilation and axiom audit
are required before these proof candidates may be treated as verified.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster

/-- Unit complex mass transfers the narrow node wedge to its complement. -/
theorem zeroBudget_canonicalNode_four_abs_im_le_one_sub_re
    (i : ActualPairIndex) :
    4 * |(canonicalNode i).im| ≤ 1 - (canonicalNode i).re := by
  have hr : HasSum (fun j : ActualPairIndex => (canonicalNode j).re) 1 := by
    simpa using Complex.hasSum_re canonicalNode_mass_one
  have hi : HasSum (fun j : ActualPairIndex => (canonicalNode j).im) 0 := by
    simpa using Complex.hasSum_im canonicalNode_mass_one
  have hp : HasSum
      (fun j : ActualPairIndex => (canonicalNode j).re + 4 * (canonicalNode j).im)
      1 := by
    simpa using hr.add (hi.mul_left 4)
  have hm : HasSum
      (fun j : ActualPairIndex => (canonicalNode j).re - 4 * (canonicalNode j).im)
      1 := by
    simpa using hr.sub (hi.mul_left 4)
  have hplus := hp.summable.le_tsum i (fun j _ => by
    have h := zeroBudget_canonicalNode_four_abs_im_le_re j
    have hneg := neg_le_abs (canonicalNode j).im
    linarith)
  have hminus := hm.summable.le_tsum i (fun j _ => by
    have h := zeroBudget_canonicalNode_four_abs_im_le_re j
    have hpos := le_abs_self (canonicalNode j).im
    linarith)
  rw [hp.tsum_eq] at hplus
  rw [hm.tsum_eq] at hminus
  have habs : |4 * (canonicalNode i).im| ≤ 1 - (canonicalNode i).re := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    4 * |(canonicalNode i).im| = |4 * (canonicalNode i).im| := by
      rw [abs_mul]
      norm_num
    _ ≤ 1 - (canonicalNode i).re := habs

/-- The actual spectral summands are nonnegative through Bernstein degree five. -/
theorem zeroBudget_spectralTerm_re_nonneg_le_five
    (N j : ℕ) (hN : N ≤ 5) (hj : j ≤ N) (i : ActualPairIndex) :
    0 ≤ (spectralTerm N j (canonicalNode i)).re := by
  have hdegree : (j + 1) + (N - j) ≤ 6 := by omega
  have hproduct := zeroBudget_re_pow_mul_one_sub_nonneg
    (canonicalNode i) (j + 1) (N - j) hdegree
    (zeroBudget_canonicalNode_four_abs_im_le_re i)
    (zeroBudget_canonicalNode_four_abs_im_le_one_sub_re i)
  have hscaled := mul_nonneg (Nat.cast_nonneg (N.choose j) :
      (0 : ℝ) ≤ (N.choose j : ℝ)) hproduct
  simpa [spectralTerm, mul_assoc, Complex.mul_re] using hscaled

/-- Canonical summation transfers finite-degree node positivity to actual weights. -/
theorem zeroBudget_actualWeight_nonneg_le_five
    (N j : ℕ) (hN : N ≤ 5) (hj : j ≤ N) :
    0 ≤ actualWeight N j := by
  have hs : HasSum
      (fun i : ActualPairIndex => (spectralTerm N j (canonicalNode i)).re)
      (actualWeight N j) := by
    simpa only [spectralTerm, actualWeight, Complex.ofReal_re] using
      Complex.hasSum_re
        (bernsteinWeight_hasSum actualNormalizedMoment canonicalNode canonicalPowerSums N j)
  rw [← hs.tsum_eq]
  exact tsum_nonneg (fun i => zeroBudget_spectralTerm_re_nonneg_le_five N j hN hj i)

/-- Every Bernstein row through degree five has total variation one. -/
theorem zeroBudget_actualVariation_eq_one_le_five
    (N : ℕ) (hN : N ≤ 5) : actualVariation N = 1 := by
  apply (rowVariation_eq_one_iff actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional N).mpr
  intro j hj
  have hjN : j ≤ N := by
    have h := Finset.mem_range.mp hj
    omega
  exact zeroBudget_actualWeight_nonneg_le_five N j hN hjN

/-- Exactly the first five cancellation indices: zero, one, two, three, four. -/
theorem zeroBudgetCandidate_first_five_cancellations
    (n : ℕ) (hn : n < 5) :
    rowCancellation actualNormalizedMoment n = 0 := by
  apply rowCancellation_eq_zero_of_rowVariation_eq
  change actualVariation (n + 1) = actualVariation n
  rw [zeroBudget_actualVariation_eq_one_le_five (n + 1) (by omega),
    zeroBudget_actualVariation_eq_one_le_five n (by omega)]

end RH_HilbertLimit
