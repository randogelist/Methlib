import RH_HilbertLimit.TwoRoutes.RouteOne

/-! The original natural cutoff/coefficient predicate, with fixed-pair equivalence. -/

set_option autoImplicit false
noncomputable section
open RH_HilbertLimit RH_HilbertLimit.TwoRoutes

namespace HXYThreeSpaces

def HXY (X Y : ℕ) : Prop := CancellationBudget.Admissible ⟨X, Y⟩

theorem nativeRH_of_HXY (X Y : ℕ) (h : HXY X Y) : _root_.RiemannHypothesis :=
  nativeRH_of_admissible_cancellationBudget ⟨X, Y⟩ h

theorem HXY_of_nativeRH (X Y : ℕ) (hRH : _root_.RiemannHypothesis) : HXY X Y := by
  intro n hn
  rw [actual_cancellation_zero_of_H00 (H00_of_nativeRH hRH) n]
  exact mul_nonneg (Nat.cast_nonneg Y) (rowVariation_nonneg actualNormalizedMoment n)

theorem HXY_iff_nativeRH (X Y : ℕ) : HXY X Y ↔ _root_.RiemannHypothesis :=
  ⟨nativeRH_of_HXY X Y, HXY_of_nativeRH X Y⟩

end HXYThreeSpaces
