import RH_HilbertLimit.ZeroBudgetTenRows

/-!
# Exact propagation frontier after the verified first ten cancellation indices

The finite analytic work through v0.2.32 establishes cancellation at indices
0 through 9. This module does not extend that finite range. Instead it removes
those ten already-settled cases from the universal admissibility obligation.

The zero budget is admissible exactly when cancellation vanishes from index ten
onward, and equivalently exactly when the one-step zero-propagation law holds
from index nine onward. Combining the existing zero-budget admissibility iff RH
theorem gives the same exact tail-propagation criterion for literal Mathlib RH.

No universal propagation law is proved here; the theorem isolates it as the
remaining analytic endpoint. Native Lean compilation and axiom audit are required.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- After the first ten verified indices, admissibility is exactly the remaining tail. -/
theorem zeroBudgetCandidate_admissible_iff_tail_from_ten :
    zeroBudgetCandidate.Admissible ↔
      ∀ n : ℕ, 10 ≤ n → rowCancellation actualNormalizedMoment n = 0 := by
  rw [zeroBudgetCandidate_admissible_iff_all_cancellation_zero]
  constructor
  · intro hall n _hn
    exact hall n
  · intro htail n
    by_cases hn : n < 10
    · exact zeroBudgetCandidate_first_ten_cancellations n hn
    · exact htail n (by omega)

/-- Since cancellation at index nine is already verified, all-order admissibility
is equivalent to one-step zero propagation beginning at index nine. -/
theorem zeroBudgetCandidate_admissible_iff_propagation_from_nine :
    zeroBudgetCandidate.Admissible ↔
      ∀ n : ℕ, 9 ≤ n →
        rowCancellation actualNormalizedMoment n = 0 →
        rowCancellation actualNormalizedMoment (n + 1) = 0 := by
  constructor
  · intro hadm n _hn _hzero
    have hall := zeroBudgetCandidate_admissible_iff_all_cancellation_zero.mp hadm
    exact hall (n + 1)
  · intro hstep
    apply zeroBudgetCandidate_admissible_iff_all_cancellation_zero.mpr
    intro n
    induction n with
    | zero =>
        exact zeroBudgetCandidate_first_ten_cancellations 0 (by omega)
    | succ n ih =>
        by_cases hn : n < 9
        · exact zeroBudgetCandidate_first_ten_cancellations (n + 1) (by omega)
        · exact hstep n (by omega) ih

/-- Literal RH is equivalent to the unresolved tail after the verified first ten. -/
theorem nativeRH_iff_zeroBudget_tail_from_ten :
    _root_.RiemannHypothesis ↔
      ∀ n : ℕ, 10 ≤ n → rowCancellation actualNormalizedMoment n = 0 :=
  zeroBudgetCandidate_admissible_iff_nativeRH.symm.trans
    zeroBudgetCandidate_admissible_iff_tail_from_ten

/-- Literal RH is equivalently the one-step propagation law from index nine onward. -/
theorem nativeRH_iff_zeroBudget_propagation_from_nine :
    _root_.RiemannHypothesis ↔
      ∀ n : ℕ, 9 ≤ n →
        rowCancellation actualNormalizedMoment n = 0 →
        rowCancellation actualNormalizedMoment (n + 1) = 0 :=
  zeroBudgetCandidate_admissible_iff_nativeRH.symm.trans
    zeroBudgetCandidate_admissible_iff_propagation_from_nine

end RH_HilbertLimit
