import Mathlib.Analysis.Analytic.Basic
import QuasiFeffermanB.Endpoints.Root

/-!
Analytic-admissible uniqueness extension for the frozen Quasi-Fefferman-B root.

The original root is not modified.  `QFBAnalyticAdmissible` records the exact
positive-time analytic and weak--strong data needed for the native physical
Serrin comparison: a Leray--Hopf trajectory, an actual normalized positive-time
NSE pressure, joint space-time analyticity, the strong initial L2 trace, and
the finite-horizon Serrin bound.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- Exact analytic-admissibility certificate.  Analyticity is asserted on the
open positive-time spacetime region; no analyticity at the initial endpoint is
assumed.  The trace and Serrin clauses are explicit rather than inferred from
an unspecified analytic-function-space closure principle. -/
structure QFBAnalyticAdmissible
    (ν : ℝ) (a : CriticalPhysicalL2)
    (u : Velocity) (G : WeakGradientTrajectory) where
  lerayHopf : CriticalLerayHopf ν a u G
  pressure : Pressure
  positiveNSE : PositiveSmoothNSE ν u pressure
  velocityAnalytic :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime
  pressureAnalytic :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => pressure z.1 z.2) positiveSpacetime
  strongTrace : Tendsto
    (fun t => eLpNorm (u t - (a : Vec → Vec)) 2
      (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0)
  serrin : ∀ T : ℝ, 0 < T →
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioc (0 : ℝ) T))

/-- Any two analytic-admissible Leray--Hopf trajectories with the same datum
coincide as physical L2 representatives at every nonnegative time. -/
theorem QFB_ANALYTIC_PAIR_UNIQUENESS
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    {u v : Velocity} {G H : WeakGradientTrajectory}
    (hu : QFBAnalyticAdmissible ν a u G)
    (hv : QFBAnalyticAdmissible ν a v H) :
    SameVelocity u v := by
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    exact hu.lerayHopf.initial.trans hv.lerayHopf.initial.symm
  · exact CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON
      ν hν a u v G hv.pressure hu.lerayHopf
      (positiveSmoothNSE_test hv.positiveNSE)
      (fun r hr => positiveSmoothNSE_pressure_spatial_smooth hv.positiveNSE hr)
      hv.positiveNSE.pressure_periodic hv.positiveNSE.equation
      hv.strongTrace t hpos (hv.serrin t hpos) t ⟨hpos, le_rfl⟩

/-- Closed universal uniqueness statement for the analytic-admissible QFB
class. -/
def QFBAnalyticUniquenessStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : CriticalPhysicalL2) (u v : Velocity)
      (G H : WeakGradientTrajectory),
      QFBAnalyticAdmissible ν a u G →
      QFBAnalyticAdmissible ν a v H →
      SameVelocity u v

/-- Exact universal analytic-admissible uniqueness endpoint. -/
theorem QFB_ANALYTIC_UNIQUENESS : QFBAnalyticUniquenessStatement := by
  intro ν hν a u v G H hu hv
  exact QFB_ANALYTIC_PAIR_UNIQUENESS hν hu hv

/-- Conservative extension of the frozen QFB root.  The original root theorem
and statement remain byte-for-byte unchanged. -/
def QuasiFeffermanBWithAnalyticUniquenessStatement : Prop :=
  QuasiFeffermanBStatement ∧ QFBAnalyticUniquenessStatement

/-- Merged QFB root plus the independent analytic-admissible uniqueness
endpoint. -/
theorem QUASI_FEFFERMAN_B_WITH_ANALYTIC_UNIQUENESS :
    QuasiFeffermanBWithAnalyticUniquenessStatement :=
  ⟨QUASI_FEFFERMAN_B_COMPOSED, QFB_ANALYTIC_UNIQUENESS⟩

end
end QuasiFeffermanB
