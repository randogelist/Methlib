import RH_HilbertLimit.ZeroBudgetTenSector
import RH_HilbertLimit.ZeroBudgetTenAlgebra

/-!
# Candidate transfer for the next five cancellation indices

This source adapts the frozen first-five row transfer to a narrower node
sector. The accompanying source includes the actual-xi analytic construction
in `ZeroBudgetTenCenter`, `ZeroBudgetTenKappa`, and `ZeroBudgetTenSector`,
together with the degree-eleven algebra in `ZeroBudgetTenAlgebra`.

Given those dependencies, unit canonical mass supplies the complementary
one-seventh wedge. Exact canonical summation then gives nonnegative Bernstein
rows through degree ten and zero cancellation at indices zero through nine.
The next-five endpoint is explicitly restricted to indices five through nine.

This is source preparation only. No Lean, native compiler, or CI was executed.
Native compilation and axiom audit of the included source remain pending;
this file does not record a verified second batch. Universal propagation,
full witness admissibility, and RH are outside its asserted finite range.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster

/-- Unit complex mass transfers the narrower node wedge to its complement. -/
theorem zeroBudget_canonicalNode_seven_abs_im_le_one_sub_re
    (i : ActualPairIndex) :
    7 * |(canonicalNode i).im| ≤ 1 - (canonicalNode i).re := by
  have hr : HasSum (fun j : ActualPairIndex => (canonicalNode j).re) 1 := by
    simpa using Complex.hasSum_re canonicalNode_mass_one
  have hi : HasSum (fun j : ActualPairIndex => (canonicalNode j).im) 0 := by
    simpa using Complex.hasSum_im canonicalNode_mass_one
  have hp : HasSum
      (fun j : ActualPairIndex => (canonicalNode j).re + 7 * (canonicalNode j).im)
      1 := by
    simpa using hr.add (hi.mul_left 7)
  have hm : HasSum
      (fun j : ActualPairIndex => (canonicalNode j).re - 7 * (canonicalNode j).im)
      1 := by
    simpa using hr.sub (hi.mul_left 7)
  have hplus := hp.summable.le_tsum i (fun j _ => by
    have h := zeroBudget_canonicalNode_seven_abs_im_le_re j
    have hneg := neg_le_abs (canonicalNode j).im
    linarith)
  have hminus := hm.summable.le_tsum i (fun j _ => by
    have h := zeroBudget_canonicalNode_seven_abs_im_le_re j
    have hpos := le_abs_self (canonicalNode j).im
    linarith)
  rw [hp.tsum_eq] at hplus
  rw [hm.tsum_eq] at hminus
  have habs : |7 * (canonicalNode i).im| ≤ 1 - (canonicalNode i).re := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    7 * |(canonicalNode i).im| = |7 * (canonicalNode i).im| := by
      rw [abs_mul]
      norm_num
    _ ≤ 1 - (canonicalNode i).re := habs

/-- Finite-degree positivity of the actual spectral summands, through degree ten. -/
theorem zeroBudget_spectralTerm_re_nonneg_le_ten
    (N j : ℕ) (hN : N ≤ 10) (hj : j ≤ N) (i : ActualPairIndex) :
    0 ≤ (spectralTerm N j (canonicalNode i)).re := by
  have hdegree : (j + 1) + (N - j) ≤ 11 := by omega
  have hproduct := zeroBudgetTen_re_pow_mul_one_sub_nonneg
    (canonicalNode i) (j + 1) (N - j) hdegree
    (zeroBudget_canonicalNode_seven_abs_im_le_re i)
    (zeroBudget_canonicalNode_seven_abs_im_le_one_sub_re i)
  have hscaled := mul_nonneg (Nat.cast_nonneg (N.choose j) :
      (0 : ℝ) ≤ (N.choose j : ℝ)) hproduct
  simpa [spectralTerm, mul_assoc, Complex.mul_re] using hscaled

/-- Exact canonical summation transfers the degree-ten sector bounds. -/
theorem zeroBudget_actualWeight_nonneg_le_ten
    (N j : ℕ) (hN : N ≤ 10) (hj : j ≤ N) :
    0 ≤ actualWeight N j := by
  have hs : HasSum
      (fun i : ActualPairIndex => (spectralTerm N j (canonicalNode i)).re)
      (actualWeight N j) := by
    simpa only [spectralTerm, actualWeight, Complex.ofReal_re] using
      Complex.hasSum_re
        (bernsteinWeight_hasSum actualNormalizedMoment canonicalNode canonicalPowerSums N j)
  rw [← hs.tsum_eq]
  exact tsum_nonneg (fun i => zeroBudget_spectralTerm_re_nonneg_le_ten N j hN hj i)

/-- Total variation one through Bernstein degree ten. -/
theorem zeroBudget_actualVariation_eq_one_le_ten
    (N : ℕ) (hN : N ≤ 10) : actualVariation N = 1 := by
  apply (rowVariation_eq_one_iff actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional N).mpr
  intro j hj
  have hjN : j ≤ N := by
    have h := Finset.mem_range.mp hj
    omega
  exact zeroBudget_actualWeight_nonneg_le_ten N j hN hjN

/-- The first ten cancellation indices, with the finite bound explicit. -/
theorem zeroBudgetCandidate_first_ten_cancellations
    (n : ℕ) (hn : n < 10) :
    rowCancellation actualNormalizedMoment n = 0 := by
  apply rowCancellation_eq_zero_of_rowVariation_eq
  change actualVariation (n + 1) = actualVariation n
  rw [zeroBudget_actualVariation_eq_one_le_ten (n + 1) (by omega),
    zeroBudget_actualVariation_eq_one_le_ten n (by omega)]

/-- The requested second batch consists exactly of indices five through nine. -/
theorem zeroBudgetCandidate_next_five_cancellations
    (n : ℕ) (hn : 5 ≤ n ∧ n < 10) :
    rowCancellation actualNormalizedMoment n = 0 := by
  exact zeroBudgetCandidate_first_ten_cancellations n hn.2

end RH_HilbertLimit
