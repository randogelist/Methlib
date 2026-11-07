import Tail16Frontier.BernsteinIntervals
import Tail16Frontier.NativeAdmission
import Tail16Frontier.BoolFacts

set_option autoImplicit false

namespace Tail16Frontier

/-- A total finite Boolean conjunction; it does not quantify computationally over Nat. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | N+1 => allBelow p N && p N

theorem allBelow_sound (p : Nat → Bool) (N : Nat)
    (h : allBelow p N = true) :
    ∀ j : Nat, j < N → p j = true := by
  revert h
  induction N with
  | zero =>
      intro h j hj
      omega
  | succ N ih =>
      intro h
      have hparts : allBelow p N = true ∧ p N = true := by
        exact Tail16Bool.andTrue h
      intro j hj
      by_cases heq : j = N
      · simpa [heq] using hparts.2
      · have hjN : j < N := by omega
        exact ih hparts.1 j hjN

theorem allBelow_complete (p : Nat → Bool) (N : Nat)
    (h : ∀ j : Nat, j < N → p j = true) :
    allBelow p N = true := by
  revert h
  induction N with
  | zero =>
      intro h
      rfl
  | succ N ih =>
      intro h
      have htail : ∀ j : Nat, j < N → p j = true := by
        intro j hj
        exact h j (by omega)
      have hlast : p N = true := h N (by omega)
      simp only [allBelow, ih htail, hlast, Bool.true_and]

/-- Exact rational cancellation-budget residual. -/
def qGap (d : MomentData) (n Y : Nat) : ℚ :=
  ((Y : ℚ)+(n : ℚ)+1) * qVariation d n -
    ((n : ℚ)+1) * qVariation d (n+1)

/-- Exact rational symmetric uncertainty budget for qGap. -/
def qGapError (d : MomentData) (n Y : Nat) : ℚ :=
  ((Y : ℚ)+(n : ℚ)+1) * rowError d n +
    ((n : ℚ)+1) * rowError d (n+1)

/-- Numerical test only. Actual moment enclosure is checked separately by the kernel. -/
def marginCheck (d : MomentData) (n Y : Nat) : Bool :=
  d.shapeCheck (n+1) &&
    decide ((0 : ℚ) ≤ qGap d n Y - qGapError d n Y)

/-- Numerical row-sign test, using the exact rational finite entrywise errors. -/
def signCheck (d : MomentData) (M : Nat) : Bool :=
  d.shapeCheck M &&
    allBelow
      (fun j => decide ((0 : ℚ) ≤ qBernstein d M j - entryError d M j))
      (M+1)

/-- Sound actual single-step admission, conditional on the separately checked enclosure. -/
theorem marginCheck_sound (d : MomentData) (n Y : Nat)
    (hdata : d.Encloses (n+1))
    (hcheck : marginCheck d n Y = true) :
    BudgetStep Y n := by
  have hparts :
      d.shapeCheck (n+1) = true ∧
        decide ((0 : ℚ) ≤ qGap d n Y - qGapError d n Y) = true :=
    Tail16Bool.andTrue hcheck
  have hq : (0 : ℚ) ≤ qGap d n Y - qGapError d n Y :=
    of_decide_eq_true hparts.2
  have hqR :
      (0 : ℝ) ≤
        ((Y : ℝ)+(n : ℝ)+1) * (qVariation d n : ℝ) -
          ((n : ℝ)+1) * (qVariation d (n+1) : ℝ) -
        (((Y : ℝ)+(n : ℝ)+1) * (rowError d n : ℝ) +
          ((n : ℝ)+1) * (rowError d (n+1) : ℝ)) := by
    unfold qGap qGapError at hq
    exact_mod_cast hq
  have hn : d.Encloses n :=
    MomentData.encloses_mono hdata (Nat.le_succ n)
  have hnerr := variation_error_bound d n hn
  have hsucerr := variation_error_bound d (n+1) hdata
  have hlo :
      (qVariation d n : ℝ) - (rowError d n : ℝ) ≤
        RH_HilbertLimit.actualVariation n := by
    have := (abs_le.mp hnerr).1
    linarith
  have hhi :
      RH_HilbertLimit.actualVariation (n+1) ≤
        (qVariation d (n+1) : ℝ) + (rowError d (n+1) : ℝ) := by
    have := (abs_le.mp hsucerr).2
    linarith
  have ha : (0 : ℝ) ≤ (Y : ℝ)+(n : ℝ)+1 := by positivity
  have hb : (0 : ℝ) ≤ (n : ℝ)+1 := by positivity
  have hmullo := mul_le_mul_of_nonneg_left hlo ha
  have hmulhi := mul_le_mul_of_nonneg_left hhi hb
  unfold BudgetStep
  rw [RH_HilbertLimit.rowCancellation_eq]
  change ((n : ℝ)+1) *
      (RH_HilbertLimit.actualVariation (n+1) -
        RH_HilbertLimit.actualVariation n) ≤
    (Y : ℝ) * RH_HilbertLimit.actualVariation n
  nlinarith [hmullo, hmulhi, hqR]

/-- Sound actual row-sign admission, conditional on the separately checked enclosure. -/
theorem signCheck_sound (d : MomentData) (M : Nat)
    (hdata : d.Encloses M)
    (hcheck : signCheck d M = true) :
    ∀ j : Nat, j ≤ M →
      0 ≤ RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment M j := by
  have hparts :
      d.shapeCheck M = true ∧
        allBelow
          (fun j => decide ((0 : ℚ) ≤ qBernstein d M j - entryError d M j))
          (M+1) = true :=
    Tail16Bool.andTrue hcheck
  intro j hj
  have hjlt : j < M+1 := by omega
  have hbool := allBelow_sound
    (fun i => decide ((0 : ℚ) ≤ qBernstein d M i - entryError d M i))
    (M+1) hparts.2 j hjlt
  have hq : (0 : ℚ) ≤ qBernstein d M j - entryError d M j :=
    of_decide_eq_true hbool
  have hqR : (0 : ℝ) ≤
      (qBernstein d M j : ℝ) - (entryError d M j : ℝ) := by
    exact_mod_cast hq
  have herr := entry_error_bound d M j hdata hj
  have hlo := (abs_le.mp herr).1
  linarith

/-- Positive control: the actual zeroth Bernstein row is certified exactly. -/
theorem zeroMomentData_signCheck : signCheck zeroMomentData 0 = true := by
  norm_num [signCheck, allBelow, MomentData.shapeCheck, qBernstein, entryError,
    zeroMomentData, MomentData.center, MomentData.radius, rationalAt,
    Finset.sum_range_succ, Nat.choose]

/-- Genuine actual first-row sign control, including nonzero enclosure radii. -/
theorem firstMomentData_signCheck : signCheck firstMomentData 1 = true := by
  norm_num [signCheck, allBelow, MomentData.shapeCheck, qBernstein, entryError,
    firstMomentData, MomentData.center, MomentData.radius, rationalAt,
    Finset.sum_range_succ, Nat.choose]

theorem firstMomentData_row_nonnegative :
    ∀ j : Nat, j ≤ 1 →
      0 ≤ RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment 1 j :=
  signCheck_sound firstMomentData 1 firstMomentData_encloses
    firstMomentData_signCheck

/-- A malformed moment packet fails before any mathematical admission. -/
def missingMomentData : MomentData :=
  { centers := [], radii := [] }

theorem missingMomentData_signCheck_rejected :
    signCheck missingMomentData 0 = false := by
  decide

/-- Actual-moment-backed single-step control with a deliberately positive budget. -/
theorem firstMomentData_marginCheck :
    marginCheck firstMomentData 0 4 = true := by
  norm_num [marginCheck, MomentData.shapeCheck, qGap, qGapError,
    qVariation, rowError, qBernstein, entryError, firstMomentData,
    MomentData.center, MomentData.radius, rationalAt,
    Finset.sum_range_succ, Nat.choose]

theorem firstMomentData_budgetStep : BudgetStep 4 0 :=
  marginCheck_sound firstMomentData 0 4 firstMomentData_encloses
    firstMomentData_marginCheck

end Tail16Frontier

