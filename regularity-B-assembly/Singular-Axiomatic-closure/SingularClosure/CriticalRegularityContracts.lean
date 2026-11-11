import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalSpacesEmbedding

/-! Exact rough-data regularity target.  These are concrete predicates, not axioms. -/
set_option autoImplicit false
open Set MeasureTheory
namespace SingularClosure
noncomputable section

/-- Real, solenoidal, zero-mean critical data on the three-dimensional torus. -/
structure CriticalSigmaZero (a : CriticalSobolev 1) : Prop where
  reality : SpectralReality (criticalCoeff 1 a)
  solenoidal : SpectralSolenoidal (criticalCoeff 1 a)
  mean_zero : SpectralMeanZero (criticalCoeff 1 a)

/-- Global critical solution with strong initial trace, actual positive-time
Sobolev NSE flow, and actual local L²H3/2 membership. No initial smoothness. -/
structure CriticalRegularSolution (ν : ℝ) (a : CriticalSobolev 1) where
  critical : ℝ → CriticalSobolev 1
  flow : CriticalPositiveSobolevFlow ν
  continuous : ContinuousOn critical (Ici 0)
  initial : critical 0 = a
  coefficient_agreement : ∀ t : ℝ, 0 < t →
    (flow.state 0 t).val = criticalCoeff 1 (critical t)
  critical_bound : ∀ t : ℝ, 0 ≤ t → ‖critical t‖ ≤ ‖a‖
  dissipation_uniform : ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 < T →
    ∃ v : ℝ → CriticalSobolev 3,
      MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff 3 (v t) = criticalCoeff 1 (critical t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2) ≤ B

/-- Existence of the exact concrete solution record. -/
def CriticalGlobalRegularity (ν : ℝ) (a : CriticalSobolev 1) : Prop :=
  Nonempty (CriticalRegularSolution ν a)

theorem CriticalRegularSolution.physicalNSE
    {ν : ℝ} {a : CriticalSobolev 1} (u : CriticalRegularSolution ν a) :
    PositiveSmoothNSE ν u.flow.velocity u.flow.pressure :=
  CRITICAL_POSITIVE_PHYSICAL_NSE u.flow

end
end SingularClosure
