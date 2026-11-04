import HVRZetaDefeqProjection
import Mathlib.MeasureTheory.Integral.Prod
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Diagnostic only; negative reachability is not semantic independence. -/
open Lean Elab Command
namespace HVRZetaDefeqProjectionTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
noncomputable def projectedDirect := @HVRZetaDefeqProjection.rawZeta
noncomputable def projectedIndirect := @projectedDirect
end HVRZetaDefeqProjectionTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let swap := `MeasureTheory.integral_integral_swap
  let controls : Array (Name × Name) := #[
    (`HVRZetaDefeqProjectionTraceControl.swapDirect, swap),
    (`HVRZetaDefeqProjectionTraceControl.swapIndirect, swap),
    (`HVRZetaDefeqProjectionTraceControl.projectedDirect, `HVRZetaDefeqProjection.rawZeta),
    (`HVRZetaDefeqProjectionTraceControl.projectedIndirect, `HVRZetaDefeqProjection.rawZeta)]
  for (root, target) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "DEFEQ_CONTROL_MISSED={root}|{target}"
    IO.println s!"DEFEQ_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[`HVRZetaDefeqProjection.zeroConstant,
    `HVRZetaDefeqProjection.rawModifiedTheta,
    `HVRZetaDefeqProjection.rawLambda,
    `HVRZetaDefeqProjection.rawZeta, `riemannZeta]
  for root in roots do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains swap then
      IO.println s!"DEFEQ_TARGET_FOUND={root}|{swap}"
    else
      IO.println s!"DEFEQ_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{swap}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"DEFEQ_REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"DEFEQ_REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
