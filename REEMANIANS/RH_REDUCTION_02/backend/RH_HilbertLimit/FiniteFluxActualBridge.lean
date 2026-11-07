import RH_HilbertLimit.FiniteFluxChecker

/-!
# Actual Bernstein-flux interpretation, with the analytic gap explicit

The finite algebraic checker from v0.2.36 is sound for a valuation of its
numbered atoms PROVIDED its weighted premises are nonnegative.  This file
specifies the missing interface with the actual Hilbert/xi Bernstein weights:

1. an exact calibration of the checked symbolic *goals* to the next-row
   cancellation and boundary slacks;
2. a positivity interpretation of the checked symbolic premises, conditional
   on the current row's `FluxGood` hypothesis.

Given these two explicit infinite semantic conditions, the checked four-region
algebra yields `FluxStepFromNine` and hence literal Mathlib RH.  Neither
semantic condition is in the finite raw witness nor is it checked by the
v0.2.36 Boolean checker.  This is NOT yet finite-witness-to-RH soundness.

No Lean, Lake, or native Windows compilation was run while preparing this file.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- Each checked next-row local inequality belongs to a finite branch.
The separate `.boundary` certificate handles the flux boundary inequality. -/
def nextLocalFluxRegion (n j : ℕ) : FluxRegion :=
  if j = 0 then FluxRegion.left
  else if j = n + 1 then FluxRegion.right
  else FluxRegion.interior

/-- The exact next-row local slack for the ACTUAL xi/Bernstein data. -/
def actualNextLocalFluxSlack
    (W : FiniteFluxCheckedWitness) (n j : ℕ) : ℝ :=
  (W.raw.coefficient : ℝ) * |actualWeight (n + 1) j| +
    (W.raw.flux (n + 1) (j + 1) - W.raw.flux (n + 1) j) -
      cancellationDefect actualNormalizedMoment (n + 1) j

/-- The exact next-row boundary slack for the ACTUAL finite flux. -/
def actualNextBoundaryFluxSlack
    (W : FiniteFluxCheckedWitness) (n : ℕ) : ℝ :=
  W.raw.flux (n + 1) 0 - W.raw.flux (n + 1) (n + 2)

/-- The checked goal must denote the actual next-row slack.  This is the
missing analytic/polynomial calibration, NOT a consequence of the current Bool
checker.  The valuation is a semantic function, not witness data. -/
def ActualFluxGoalCalibration
    (W : FiniteFluxCheckedWitness) (ρ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ n j : ℕ, 9 ≤ n → j ≤ n + 1 →
    (W.regions.get (nextLocalFluxRegion n j)).goal.eval (ρ n j) =
      actualNextLocalFluxSlack W n j) ∧
  (∀ n : ℕ, 9 ≤ n →
    (W.regions.get FluxRegion.boundary).goal.eval (ρ n (n + 2)) =
      actualNextBoundaryFluxSlack W n)

/-- The checked premises must be genuinely nonnegative for the actual data,
under the current good-row hypothesis.  This is a second open semantic bridge:
a syntactic weighted-sum identity cannot prove nonnegativity of arbitrary
user-supplied premises. -/
def ActualFluxPremisePositivity
    (W : FiniteFluxCheckedWitness) (ρ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ n j : ℕ, 9 ≤ n → j ≤ n + 1 →
    (finiteFluxBudget W.raw.coefficient).FluxGood W.raw.flux n →
    ∀ t ∈ (W.regions.get (nextLocalFluxRegion n j)).terms,
      0 ≤ t.evalTerm (ρ n j)) ∧
  (∀ n : ℕ, 9 ≤ n →
    (finiteFluxBudget W.raw.coefficient).FluxGood W.raw.flux n →
    ∀ t ∈ (W.regions.get FluxRegion.boundary).terms,
      0 ≤ t.evalTerm (ρ n (n + 2)))

/-- Combined actual interpretation interface, deliberately separate from raw
finite data and the executable Bool checker. -/
def ActualFluxInterpretation
    (W : FiniteFluxCheckedWitness) (ρ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ActualFluxGoalCalibration W ρ ∧ ActualFluxPremisePositivity W ρ

namespace FiniteFluxCheckedWitness

/-- The real-valued interpretation of the four checked finite certificates
transfers an accepted algebraic certificate to the actual uniform flux step.
The interpretation assumptions are explicit and remain OPEN. -/
theorem stepSound_of_actualFluxInterpretation
    (W : FiniteFluxCheckedWitness)
    (hcheck : W.check = true)
    (ρ : ℕ → ℕ → ℕ → ℝ)
    (hI : ActualFluxInterpretation W ρ) :
    W.StepSound := by
  rcases hI with ⟨⟨hgoal, hboundary⟩, ⟨hprem, hpremBoundary⟩⟩
  change FluxStepFromNine W.raw.coefficient W.raw.flux
  intro n hn hgood
  change (finiteFluxBudget W.raw.coefficient).FluxGood W.raw.flux (n + 1)
  constructor
  · intro j hj
    have hterms :
        ∀ t ∈ (W.regions.get (nextLocalFluxRegion n j)).terms,
          0 ≤ t.evalTerm (ρ n j) := hprem n j hn hj hgood
    have hnonneg :
        0 ≤ (W.regions.get (nextLocalFluxRegion n j)).goal.eval (ρ n j) :=
      W.region_sound hcheck (nextLocalFluxRegion n j) (ρ n j) hterms
    rw [hgoal n j hn hj] at hnonneg
    unfold actualNextLocalFluxSlack at hnonneg
    -- Definitionally unfold the finite budget coefficient before applying
    -- the exact order equivalence `0 ≤ a - b ↔ b ≤ a`.
    -- `linarith` cannot see through the record projection automatically.
    change cancellationDefect actualNormalizedMoment (n + 1) j ≤
      (W.raw.coefficient : ℝ) * |actualWeight (n + 1) j| +
        (W.raw.flux (n + 1) (j + 1) - W.raw.flux (n + 1) j)
    exact sub_nonneg.mp hnonneg
  · have hterms :
        ∀ t ∈ (W.regions.get FluxRegion.boundary).terms,
          0 ≤ t.evalTerm (ρ n (n + 2)) := hpremBoundary n hn hgood
    have hnonneg :
        0 ≤ (W.regions.get FluxRegion.boundary).goal.eval (ρ n (n + 2)) :=
      W.region_sound hcheck FluxRegion.boundary (ρ n (n + 2)) hterms
    rw [hboundary n hn] at hnonneg
    unfold actualNextBoundaryFluxSlack at hnonneg
    change W.raw.flux (n + 1) (n + 2) ≤ W.raw.flux (n + 1) 0
    exact sub_nonneg.mp hnonneg

/-- The exact v0.2.36 checker-soundness target follows CONDITIONALLY from the
actual interpretation.  This is not an unconditional checker-soundness proof. -/
theorem checkerSoundnessTarget_of_actualFluxInterpretation
    (W : FiniteFluxCheckedWitness)
    (ρ : ℕ → ℕ → ℕ → ℝ)
    (hI : ActualFluxInterpretation W ρ) :
    W.CheckerSoundnessTarget := by
  intro hcheck
  exact W.stepSound_of_actualFluxInterpretation hcheck ρ hI

/-- Checked finite algebra plus the still-open actual interpretation implies
literal Mathlib RH by the previously audited semantic induction endpoint. -/
theorem nativeRH_of_checked_actualFluxInterpretation
    (W : FiniteFluxCheckedWitness)
    (hcheck : W.check = true)
    (ρ : ℕ → ℕ → ℕ → ℝ)
    (hI : ActualFluxInterpretation W ρ) :
    _root_.RiemannHypothesis := by
  exact W.nativeRH_of_stepSound
    (W.stepSound_of_actualFluxInterpretation hcheck ρ hI)

end FiniteFluxCheckedWitness

/-- Existential form that displays the remaining NONFINITE semantic premise.
This does not yet prove `(exists W, W.check = true) -> RH`. -/
theorem nativeRH_of_exists_checked_finiteFlux_with_actualInterpretation
    (h : ∃ W : FiniteFluxCheckedWitness, W.check = true ∧
      ∃ ρ : ℕ → ℕ → ℕ → ℝ, ActualFluxInterpretation W ρ) :
    _root_.RiemannHypothesis := by
  obtain ⟨W, hcheck, ρ, hI⟩ := h
  exact W.nativeRH_of_checked_actualFluxInterpretation hcheck ρ hI

end RH_HilbertLimit
