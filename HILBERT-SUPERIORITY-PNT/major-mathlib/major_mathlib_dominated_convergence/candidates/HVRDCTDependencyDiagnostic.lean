import HVRCompactBoundaryLimit
import HVRDCTTraceControlBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
DIAGNOSTIC ONLY: the target is imported here after the candidate object has
been built, in order to make it visible to the diagnostic. The positive
controls intentionally depend on the target and are not imported by the
candidate. Negative findings are scoped syntactic observations and do not
prove semantic independence or absence of equivalent endpoints.
-/
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`MeasureTheory.tendsto_integral_of_dominated_convergence,
    `MeasureTheory.tendsto_integral_filter_of_dominated_convergence]
  let targetModule : Name := `Mathlib.MeasureTheory.Integral.DominatedConvergence
  let controls : Array (Name × Name) := #[
    (`HVRDCTTraceControlLeaf.direct_target,
      `MeasureTheory.tendsto_integral_of_dominated_convergence),
    (`HVRDCTTraceControlBridge.indirect_target,
      `MeasureTheory.tendsto_integral_of_dominated_convergence),
    (`HVRDCTTraceControlLeaf.direct_filter_target,
      `MeasureTheory.tendsto_integral_filter_of_dominated_convergence),
    (`HVRDCTTraceControlBridge.indirect_filter_target,
      `MeasureTheory.tendsto_integral_filter_of_dominated_convergence)]
  let roots : Array Name := #[`HVRCompactBoundaryLimit.frequency_integral_tendsto_boundary]
  for target in targets do
    if (env.find? target).isNone then
      throwError "TARGET_UNKNOWN={target}"
  for (root, target) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
    else
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
  for root in roots do
    if (env.find? root).isNone then
      throwError "ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for target in targets do
      if deps.contains target then
        IO.println s!"TARGET_FOUND={root}|{target}"
      else
        IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hiddenTheorems : Nat := 0
    let mut missingDecls : Nat := 0
    let mut sameModule : Nat := 0
    for n in deps do
      match env.find? n with
      | none =>
        missingDecls := missingDecls + 1
        IO.println s!"REACHED_DECLARATION_MISSING={root}|{n}"
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then
          hiddenTheorems := hiddenTheorems + 1
        if env.getModuleFor? n == some targetModule then
          sameModule := sameModule + 1
          IO.println s!"TARGET_MODULE_DECLARATION={root}|{n}"
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hiddenTheorems}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missingDecls}"
    IO.println s!"TARGET_MODULE_DECLARATIONS_COUNT={root}|{sameModule}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
