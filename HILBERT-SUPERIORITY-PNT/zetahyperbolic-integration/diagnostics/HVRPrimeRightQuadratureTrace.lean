import HVRPrimeRightCompactSupport
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Positive controls and coverage-limited transitive trace for the exact
right-frequency quadrature candidates. This does not replace axiom audits. -/
open Lean Elab Command

namespace HVRPrimeRightQuadratureTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRPrimeRightQuadratureTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  let controls : Array Name := #[
    `HVRPrimeRightQuadratureTraceControl.direct,
    `HVRPrimeRightQuadratureTraceControl.indirect]
  if (env.find? target).isNone then throwError "TARGET_UNKNOWN={target}"
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[
    `HVRPrimeRightQuadrature.gridCells_union_eq_interval,
    `HVRPrimeRightQuadrature.sampledRightGrid_tendsto_interval,
    `HVRPrimeRightQuadrature.sampledRightGrid_tendsto_full,
    `HVRPrimeRightCompactSupport.exists_grid_support_radius,
    `HVRPrimeRightCompactSupport.exists_compact_right_grid_limit]
  for root in roots do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"TARGET_FOUND={root}|{target}"
    else
      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
