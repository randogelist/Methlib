import RH_HilbertLimit.ActualCancellationWitness

/-!
# Native actual-xi finite-prefix and universal-tail admission

This module has no numerical source oracle and no kernel self-soundness
claim. Universal tail proofs are explicit native Lean inputs. The existing
backend accepts an arbitrary cutoff; a finite prefix is needed only when
normalizing the admitted budget to the frozen cutoff 16.

Prepared for external native Lean 4.33.0 compilation. No local Lean run.
-/

set_option autoImplicit false

namespace Tail16Frontier

def BudgetStep (Y n : Nat) : Prop :=
  RH_HilbertLimit.rowCancellation
      RH_HilbertLimit.actualNormalizedMoment n ≤
    (Y : ℝ) * RH_HilbertLimit.actualVariation n

def Prefix (Y M : Nat) : Prop :=
  ∀ n : Nat, 16 ≤ n → n < M → BudgetStep Y n

def Tail (Y M : Nat) : Prop :=
  ∀ n : Nat, M ≤ n → BudgetStep Y n

/-- An exact definitional identification, with no extra analytic premise. -/
theorem tail_iff_admissible (Y M : Nat) :
    Tail Y M ↔
      (RH_HilbertLimit.CancellationBudget.mk M Y).Admissible := by
  rfl

/-- The backend accepts any cutoff, not only the frozen cutoff 16. -/
theorem tail_nativeRH (Y M : Nat) (hTail : Tail Y M) :
    _root_.RiemannHypothesis := by
  exact RH_HilbertLimit.nativeRH_of_admissible_cancellationBudget
    ⟨M, Y⟩ ((tail_iff_admissible Y M).mp hTail)

/-- Native finite-prefix and universal-tail composition at cutoff 16. -/
theorem prefix_tail_admissible16
    (Y M : Nat) (hPrefix : Prefix Y M) (hTail : Tail Y M) :
    (RH_HilbertLimit.CancellationBudget.mk 16 Y).Admissible := by
  intro n hn
  by_cases hlt : n < M
  · exact hPrefix n hn hlt
  · exact hTail n (Nat.le_of_not_gt hlt)

theorem prefix_tail_nativeRH
    (Y M : Nat) (hPrefix : Prefix Y M) (hTail : Tail Y M) :
    _root_.RiemannHypothesis := by
  exact RH_HilbertLimit.nativeRH_of_admissible_cancellationBudget
    ⟨16, Y⟩ (prefix_tail_admissible16 Y M hPrefix hTail)

/-- The empty prefix is a finite control, not a universal tail proof. -/
theorem emptyPrefix (Y : Nat) : Prefix Y 16 := by
  intro n hn hlt
  omega

/-- Normalization is supplied by the fixed actual canonical calibration. -/
theorem actualMoment_zero_eq_one :
    RH_HilbertLimit.actualNormalizedMoment 0 = 1 := by
  exact RH_HilbertLimit.actualNormalizedMoment_zero
    (ne_of_gt RH_HilbertLimit.actualCanonicalCalibration.kappa_pos)

/-- A nonnegative maximum row forces variation one for every earlier row. -/
theorem variation_eq_one_of_nonnegative_row
    (M : Nat)
    (hrow : ∀ j : Nat, j ≤ M →
      0 ≤ RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment M j) :
    ∀ r : Nat, r ≤ M → RH_HilbertLimit.actualVariation r = 1 := by
  have htop :
      RH_HilbertLimit.rowVariation
        RH_HilbertLimit.actualNormalizedMoment M = 1 := by
    apply (RH_HilbertLimit.rowVariation_eq_one_iff
      RH_HilbertLimit.actualNormalizedMoment actualMoment_zero_eq_one M).mpr
    intro j hj
    exact hrow j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  intro r hr
  have hlo : 1 ≤ RH_HilbertLimit.rowVariation
      RH_HilbertLimit.actualNormalizedMoment r :=
    RH_HilbertLimit.one_le_rowVariation
      RH_HilbertLimit.actualNormalizedMoment actualMoment_zero_eq_one r
  have hhi : RH_HilbertLimit.rowVariation
      RH_HilbertLimit.actualNormalizedMoment r ≤ 1 := by
    calc
      RH_HilbertLimit.rowVariation
          RH_HilbertLimit.actualNormalizedMoment r ≤
        RH_HilbertLimit.rowVariation
          RH_HilbertLimit.actualNormalizedMoment M :=
        RH_HilbertLimit.rowVariation_monotone
          RH_HilbertLimit.actualNormalizedMoment hr
      _ = 1 := htop
  change RH_HilbertLimit.rowVariation
    RH_HilbertLimit.actualNormalizedMoment r = 1
  exact le_antisymm hhi hlo

/-- The maximum-row sign certificate proves exact zero cancellation below it. -/
theorem cancellation_eq_zero_of_nonnegative_row
    (M : Nat)
    (hrow : ∀ j : Nat, j ≤ M →
      0 ≤ RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment M j) :
    ∀ n : Nat, n < M →
      RH_HilbertLimit.rowCancellation
        RH_HilbertLimit.actualNormalizedMoment n = 0 := by
  intro n hn
  have hv := variation_eq_one_of_nonnegative_row M hrow
  apply RH_HilbertLimit.rowCancellation_eq_zero_of_rowVariation_eq
  change RH_HilbertLimit.actualVariation (n + 1) =
    RH_HilbertLimit.actualVariation n
  exact (hv (n + 1) (Nat.succ_le_of_lt hn)).trans
    (hv n (Nat.le_of_lt hn)).symm

/-- One maximum-row sign certificate supplies every finite prefix budget. -/
theorem prefix_of_nonnegative_row
    (Y M : Nat)
    (hrow : ∀ j : Nat, j ≤ M →
      0 ≤ RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment M j) :
    Prefix Y M := by
  intro n _hn hnM
  unfold BudgetStep
  rw [cancellation_eq_zero_of_nonnegative_row M hrow n hnM]
  exact mul_nonneg (Nat.cast_nonneg Y)
    (RH_HilbertLimit.rowVariation_nonneg
      RH_HilbertLimit.actualNormalizedMoment n)

/--
The typed output of native tail-proof admission. This structure is not a
raw byte decoder: its proof field must be supplied and checked by Lean.
-/
structure NativeTailAdmission where
  coefficient : Nat
  cutoff : Nat
  tail : Tail coefficient cutoff

theorem NativeTailAdmission.nativeRH (w : NativeTailAdmission) :
    _root_.RiemannHypothesis := by
  exact tail_nativeRH w.coefficient w.cutoff w.tail

/-- Typed output when the protocol also requests the frozen finite prefix. -/
structure NativePrefixTailAdmission where
  coefficient : Nat
  cutoff : Nat
  prefixProof : Prefix coefficient cutoff
  tail : Tail coefficient cutoff

theorem NativePrefixTailAdmission.admissible16
    (w : NativePrefixTailAdmission) :
    (RH_HilbertLimit.CancellationBudget.mk 16 w.coefficient).Admissible := by
  exact prefix_tail_admissible16
    w.coefficient w.cutoff w.prefixProof w.tail

theorem NativePrefixTailAdmission.nativeRH
    (w : NativePrefixTailAdmission) :
    _root_.RiemannHypothesis := by
  exact prefix_tail_nativeRH
    w.coefficient w.cutoff w.prefixProof w.tail

/-- Existence includes the checked native universal proof, not just coordinates. -/
theorem nativeRH_of_exists_nativeTailAdmission
    (h : Nonempty NativeTailAdmission) : _root_.RiemannHypothesis := by
  rcases h with ⟨w⟩
  exact w.nativeRH

end Tail16Frontier

