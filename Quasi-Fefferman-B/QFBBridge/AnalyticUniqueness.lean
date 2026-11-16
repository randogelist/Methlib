import Mathlib.Analysis.Analytic.Basic
import QFBBridge.FeffermanBClosure

/-!
Analytic uniqueness extension for the frozen Quasi-Fefferman-B root.

The mathematical endpoint requires only one of two Leray--Hopf trajectories
with the same smooth datum to be jointly space-time analytic for positive
time.  The finite-horizon Serrin implication needed by the native physical
weak--strong comparison is isolated as the explicit analytic-admissibility
principle `QFBAnalyticAdmissibilityPrincipleAt`; it is not silently inserted
into the uniqueness conclusion.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- Joint real analyticity of a velocity field on positive spacetime.  No
analyticity at the initial endpoint is asserted. -/
def QFBPositiveSpaceTimeAnalytic (u : Velocity) : Prop :=
  AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime

/-- Named bridge from positive-time analyticity of an actual Leray--Hopf NSE
trajectory to the finite-horizon Serrin integrability consumed by the existing
physical weak--strong comparison theorem. -/
def QFBAnalyticAdmissibilityPrincipleAt
    (ν : ℝ) (a : CriticalPhysicalL2) : Prop :=
  ∀ (u : Velocity) (G : WeakGradientTrajectory) (p : Pressure),
    CriticalLerayHopf ν a u G →
    PositiveSmoothNSE ν u p →
    QFBPositiveSpaceTimeAnalytic u →
    ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
        (volume.restrict (Ioc (0 : ℝ) T))

/-- Exact mathematical uniqueness conclusion at fixed viscosity and datum:
only the first Leray--Hopf trajectory is required to possess an actual
positive-time analytic NSE representative. -/
def QFBAnalyticUniquenessAt
    (ν : ℝ) (a : CriticalPhysicalL2) : Prop :=
  ∀ (u v : Velocity) (G H : WeakGradientTrajectory) (p : Pressure),
    CriticalLerayHopf ν a u G →
    CriticalLerayHopf ν a v H →
    PositiveSmoothNSE ν u p →
    QFBPositiveSpaceTimeAnalytic u →
    SameVelocity u v

/-- The native weak--strong theorem closes analytic uniqueness once the named
analytic-admissibility bridge is supplied. -/
theorem QFB_ANALYTIC_UNIQUENESS_AT_OF_AAP
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    (_ha : SmoothInitialDatum a)
    (hAAP : QFBAnalyticAdmissibilityPrincipleAt ν a) :
    QFBAnalyticUniquenessAt ν a := by
  intro u v G H p hu hv hNSE hAnalytic
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    exact hu.initial.trans hv.initial.symm
  · have hcomparison := CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON
      ν hν a v u H p hv
      (positiveSmoothNSE_test hNSE)
      (fun r hr => positiveSmoothNSE_pressure_spatial_smooth hNSE hr)
      hNSE.pressure_periodic hNSE.equation hu.strong_trace
      t hpos (hAAP u G p hu hNSE hAnalytic t hpos)
    exact (hcomparison t ⟨hpos, le_rfl⟩).symm

/-- Universal analytic-uniqueness implication.  Its sole unresolved analytic
endpoint is explicit in the `QFBAnalyticAdmissibilityPrincipleAt` premise. -/
def QFBAnalyticUniquenessStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : CriticalPhysicalL2), SmoothInitialDatum a →
      QFBAnalyticAdmissibilityPrincipleAt ν a →
      QFBAnalyticUniquenessAt ν a

/-- Exact scoped analytic uniqueness theorem. -/
theorem QFB_ANALYTIC_UNIQUENESS : QFBAnalyticUniquenessStatement := by
  intro ν hν a ha hAAP
  exact QFB_ANALYTIC_UNIQUENESS_AT_OF_AAP hν ha hAAP

/-- Conservative additive package: the frozen QFB root is unchanged and the
analytic uniqueness implication is adjoined as an independent endpoint. -/
def QFBAnalyticUniqueMergedStatement : Prop :=
  QuasiFeffermanBStatement ∧ QFBAnalyticUniquenessStatement

/-- Merged QFB root and analytic uniqueness implication. -/
theorem QFB_ANALYTIC_UNIQUE : QFBAnalyticUniqueMergedStatement :=
  ⟨QUASI_FEFFERMAN_B_COMPOSED, QFB_ANALYTIC_UNIQUENESS⟩

/-- Descriptive alias for the merged endpoint. -/
theorem QUASI_FEFFERMAN_B_WITH_ANALYTIC_UNIQUENESS :
    QFBAnalyticUniqueMergedStatement :=
  QFB_ANALYTIC_UNIQUE

end
end QuasiFeffermanB
