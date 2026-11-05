import ShiftAnalytic
import ShiftCore

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace Fefferman.ConcreteReal.AdjustedA

noncomputable section

/-- Classical solenoidal Schwartz seed with Euclidean L³ norm less than ε·ν.
The integral is paired with integrability because Lebesgue integration is total. -/
structure SmallSchwartzSeed (ε : ℝ) (ν : PositiveViscosity realAnalysis)
    (b : RInitial) : Prop where
  smooth : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => b x i)
  solenoidal : initialDivergenceFree realAnalysis b
  decay : clause04 realAnalysis b
  integrableCube : Integrable (fun x => (euclideanNorm3 (b x)) ^ (3 : ℕ))
  smallCube : (∫ x, (euclideanNorm3 (b x)) ^ (3 : ℕ)) < (ε * ν.val) ^ (3 : ℕ)

/-- Properties of the earlier physical trajectory. Analyticity is required only
at positive elapsed time. At elapsed time zero the seed can be merely smooth. -/
structure GlobalPositiveFlow (ν : PositiveViscosity realAnalysis) (b : RInitial)
    (s : Solution realAnalysis) : Prop where
  momentum : clause01 realAnalysis ν (zeroForce realAnalysis) s
  solenoidal : clause02 realAnalysis s
  initial : clause03 realAnalysis b s
  smoothVelocity : ∀ i : Fin 3,
    ContDiffOn ℝ ∞ (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
      {z : RSpace × ℝ | 0 ≤ z.2}
  analyticVelocity : ∀ i : Fin 3,
    ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
      {z : RSpace × ℝ | 0 < z.2}
  analyticPressure : ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.pressure z.1 z.2)
      {z : RSpace × ℝ | 0 < z.2}
  energy : clause07 realAnalysis s

/-- An exhibited strictly positive-time state of a small unforced flow. -/
def PositiveTimeState (ε : ℝ) (ν : PositiveViscosity realAnalysis)
    (u₀ : RInitial) : Prop :=
  ∃ (b : RInitial) (τ : ℝ) (s : Solution realAnalysis),
    SmallSchwartzSeed ε ν b ∧ 0 < τ ∧ GlobalPositiveFlow ν b s ∧
    shiftInitial s τ = u₀

/-- The actual shifted velocity and pressure satisfy all five whole-space
clauses. The datum is the earlier trajectory's value at time τ. -/
theorem shifted_global_solution (ν : PositiveViscosity realAnalysis)
    (b : RInitial) (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 < τ)
    (hs : GlobalPositiveFlow ν b s) :
    globalSolution realAnalysis .wholeSpace ν (shiftInitial s τ)
      (zeroForce realAnalysis) (shiftSolution s τ) := by
  refine ⟨shift_clause01 ν s τ hτ.le hs.momentum,
    shift_clause02 s τ hτ.le hs.solenoidal, shift_clause03 s τ, ?_,
    shift_clause07 s τ hτ.le hs.energy⟩
  constructor
  · intro i
    exact smoothClosedHalfSpaceReal_shift (fun x t => s.velocity x t i)
      τ hτ (hs.analyticVelocity i)
  · exact smoothClosedHalfSpaceReal_shift (fun x t => s.pressure x t) τ hτ hs.analyticPressure

/-- Fefferman A restricted at the original admissible datum u₀. The output
is the original v0.25.0 hasGlobalSolution with zero force. -/
def Fefferman_adjusted_A (ε : ℝ) : Prop :=
  ∀ (ν : PositiveViscosity realAnalysis) (u₀ : RInitial),
    admissibleInitial realAnalysis .wholeSpace u₀ →
    PositiveTimeState ε ν u₀ →
    hasGlobalSolution realAnalysis .wholeSpace ν u₀ (zeroForce realAnalysis)

/-- Compatibility with the first release of the positive-time package. -/
abbrev AdjustedFeffermanA (ε : ℝ) : Prop := Fefferman_adjusted_A ε

theorem FEF_A_POSITIVE_TIME (ε : ℝ) : Fefferman_adjusted_A ε := by
  intro ν u₀ _hadm hu₀
  rcases hu₀ with ⟨b, τ, s, _, hτ, hs, htrace⟩
  subst u₀
  exact ⟨shiftSolution s τ, shifted_global_solution ν b s τ hτ hs⟩

/- The following independent input specifies just a finite unforced history.
It contains no assumption about times beyond τ. -/

def smoothOnSlab (τ : ℝ) (f : RSpace → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : RSpace × ℝ => f z.1 z.2)
    {z : RSpace × ℝ | 0 ≤ z.2 ∧ z.2 ≤ τ}

structure FiniteHistory (ν : PositiveViscosity realAnalysis) (b : RInitial)
    (τ : ℝ) (s : Solution realAnalysis) : Prop where
  initial : clause03 realAnalysis b s
  velocitySmooth : ∀ i : Fin 3, smoothOnSlab τ (fun x t => s.velocity x t i)
  pressureSmooth : smoothOnSlab τ (fun x t => s.pressure x t)
  momentum : ∀ (x : RSpace) (t : ℝ), 0 < t → t < τ → ∀ i : Fin 3,
    timeDerivative (fun r => s.velocity x r i) t +
      sum3 realAnalysis (fun j => s.velocity x t j *
        spatialDerivative j (fun y => s.velocity y t i) x) =
        ν.val * laplacian realAnalysis (fun y => s.velocity y t i) x -
          spatialDerivative i (fun y => s.pressure y t) x
  solenoidal : ∀ (x : RSpace) (t : ℝ), 0 < t → t < τ →
    sum3 realAnalysis (fun i => spatialDerivative i (fun y => s.velocity y t i) x) = 0
  energy : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ τ →
    squareIntegrableReal (fun x => s.velocity x t) ∧
    integralNormSqReal (fun x => s.velocity x t) < C

def FinitePositiveTimeState (ε : ℝ) (ν : PositiveViscosity realAnalysis)
    (u₀ : RInitial) : Prop :=
  ∃ (b : RInitial) (τ : ℝ) (s : Solution realAnalysis),
    SmallSchwartzSeed ε ν b ∧ 0 < τ ∧ FiniteHistory ν b τ s ∧
    shiftInitial s τ = u₀

/-- Small-data existence, positive-time regularity and agreement with finite
histories at their endpoints. This Prop is an explicit input, never an axiom. -/
def SeedExtension (ε : ℝ) : Prop :=
  ∀ (ν : PositiveViscosity realAnalysis) (b : RInitial), SmallSchwartzSeed ε ν b →
    ∃ s : Solution realAnalysis, GlobalPositiveFlow ν b s ∧
      ∀ (τ : ℝ) (h : Solution realAnalysis), 0 < τ → FiniteHistory ν b τ h →
        shiftInitial s τ = shiftInitial h τ

theorem regularity_of_seed_extension (ε : ℝ) (ext : SeedExtension ε)
    (ν : PositiveViscosity realAnalysis) (u₀ : RInitial)
    (hadm : admissibleInitial realAnalysis .wholeSpace u₀)
    (hu₀ : FinitePositiveTimeState ε ν u₀) :
    hasGlobalSolution realAnalysis .wholeSpace ν u₀ (zeroForce realAnalysis) := by
  rcases hu₀ with ⟨b, τ, h, hb, hτ, hh, htrace⟩
  rcases ext ν b hb with ⟨s, hs, hmatch⟩
  apply FEF_A_POSITIVE_TIME ε ν u₀ hadm
  exact ⟨b, τ, s, hb, hτ, hs, (hmatch τ h hτ hh).trans htrace⟩

end
end Fefferman.ConcreteReal.AdjustedA
