import QuasiFeffermanB.Endpoints.Root

/-!
Conditional Fefferman--B closure from the established Quasi-Fefferman--B
root and one named restart-overlap premise.

The analytic overlap premise is represented by `QFBOneRestartOverlapStatement`.
The implication theorem is axiom-free beyond the standard axioms inherited
from the proved QFB root.  The actual named analytic axiom is isolated in
`QFBAdmissions.OneRestartOverlapAxiom`.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- A physical `L²` datum with a smooth periodic representative and the
standard divergence-free, mean-zero physical constraints. -/
structure SmoothInitialDatum (a : CriticalPhysicalL2) : Prop where
  sigma_zero : EnergySigmaZero a
  representative : Field
  representative_L2 : MemLp representative 2 (volume.restrict unitCube)
  representative_eq : criticalL2Representative representative = a
  representative_smooth : ContDiff ℝ ∞ representative
  representative_periodic : SpatialPeriodic representative

/-- A normalized global classical solution, including its actual initial
physical `L²` trace. -/
structure GlobalClassicalSolution (ν : ℝ) (a : CriticalPhysicalL2) : Prop where
  velocity : Velocity
  pressure : Pressure
  classical : ClassicalTail ν 0 velocity pressure
  initial : velocity 0 =ᵐ[volume.restrict unitCube] (a : Vec → Vec)

/-- Fefferman--B at one fixed viscosity. -/
def FeffermanBAt (ν : ℝ) : Prop :=
  ∀ a : CriticalPhysicalL2, SmoothInitialDatum a → GlobalClassicalSolution ν a

/-- The universal Fefferman--B statement over positive viscosities. -/
def FeffermanBStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → FeffermanBAt ν

/-- One regular restart whose QFB tail begins strictly before the local
classical interval ends.  `local_overlap_closes` is the formal endpoint of
local weak--strong identification and smooth overlap patching. -/
structure OneRestartOverlapCertificate
    (ν : ℝ) (a : CriticalPhysicalL2)
    (u : Velocity) (G : WeakGradientTrajectory) : Prop where
  restartTime : ℝ
  tailLag : ℝ
  localEnd : ℝ
  restart_nonneg : 0 ≤ restartTime
  tailLag_pos : 0 < tailLag
  strict_overlap : restartTime + tailLag < localEnd
  trace_sigma_zero :
    EnergySigmaZero (criticalL2Representative (u restartTime))
  restart :
    CriticalLerayHopf ν (criticalL2Representative (u restartTime))
      (Shift restartTime u) (fun t => G (restartTime + t))
  cutoff_crossed :
    cutoff (criticalL2Representative (u restartTime)) ν < tailLag
  local_overlap_closes :
    HasSmoothTail ν (Shift restartTime u) tailLag → HasSmoothTail ν u 0

/-- Every smooth datum and every Leray--Hopf trajectory has one restart
certificate.  This is the exact named unresolved analytic premise. -/
def QFBOneRestartOverlap (ν : ℝ) : Prop :=
  ∀ (a : CriticalPhysicalL2), SmoothInitialDatum a →
    ∀ (u : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν a u G →
        OneRestartOverlapCertificate ν a u G

def QFBOneRestartOverlapStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → QFBOneRestartOverlap ν

/-- QFB plus one restart-overlap certificate closes Fefferman--B at the
specified viscosity. -/
theorem feffermanBAt_of_qfb_one_restart_overlap
    (hQFB : QuasiFeffermanBStatement)
    (ν : ℝ) (hν : 0 < ν)
    (hOverlap : QFBOneRestartOverlap ν) :
    FeffermanBAt ν := by
  intro a ha
  obtain ⟨u, G, hLH⟩ := (hQFB ν hν a ha.sigma_zero).1
  let cert := hOverlap a ha u G hLH
  have hShiftQFB :=
    (hQFB ν hν (criticalL2Representative (u cert.restartTime))
      cert.trace_sigma_zero).2
      (Shift cert.restartTime u)
      (fun t => G (cert.restartTime + t))
      cert.restart
  have hShiftTail : HasSmoothTail ν (Shift cert.restartTime u) cert.tailLag :=
    (hShiftQFB.2 cert.tailLag cert.cutoff_crossed).1
  have hGlobal : HasSmoothTail ν u 0 :=
    cert.local_overlap_closes hShiftTail
  obtain ⟨v, p, hClassical, hAgreement⟩ := hGlobal
  refine ⟨v, p, hClassical, ?_⟩
  exact (hAgreement 0 le_rfl).symm.trans hLH.initial

/-- Exact conditional closure over all positive viscosities.  The established
QFB root is internal; the only explicit premise is the named overlap
statement. -/
theorem FEFFERMAN_B_OF_QFB_ONE_RESTART_OVERLAP
    (hOverlap : QFBOneRestartOverlapStatement) :
    FeffermanBStatement := by
  intro ν hν
  exact feffermanBAt_of_qfb_one_restart_overlap
    QUASI_FEFFERMAN_B_COMPOSED ν hν (hOverlap ν hν)

end
end QuasiFeffermanB
