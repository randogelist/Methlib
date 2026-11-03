import HVRCompactBoundaryLimit
import HVRDCTTraceControlBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
Diagnostic only. The selected Mathlib endpoints are deliberately imported
here after production candidate objects have been built. The two controls
are also imported solely to test that traversal observes actual uses.
The printed graph path is syntactic, not a certificate of absence of other
paths or equivalent theorems. No production proof imports this file.
-/
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`MeasureTheory.tendsto_integral_of_dominated_convergence,
    `MeasureTheory.tendsto_integral_filter_of_dominated_convergence]
  let controls : Array (Name × Name) := #[
    (`HVRDCTTraceControlLeaf.direct_target,
      `MeasureTheory.tendsto_integral_of_dominated_convergence),
    (`HVRDCTTraceControlBridge.indirect_target,
      `MeasureTheory.tendsto_integral_of_dominated_convergence),
    (`HVRDCTTraceControlLeaf.direct_filter_target,
      `MeasureTheory.tendsto_integral_filter_of_dominated_convergence),
    (`HVRDCTTraceControlBridge.indirect_filter_target,
      `MeasureTheory.tendsto_integral_filter_of_dominated_convergence)]
  for (root, target) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
    else
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
  let root : Name := `HVRCompactBoundaryLimit.frequency_integral_tendsto_boundary
  for target in targets do
    let mut queue : Array (Name × List Name) := #[(root, [root])]
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut i : Nat := 0
    let mut found := false
    while i < queue.size do
      if found then
        break
      let (current, path) := queue[i]!
      i := i + 1
      if current == target then
        found := true
        IO.println s!"SHORTEST_DEPENDENCY_PATH={root}|{target}|{String.intercalate " -> " (path.reverse.map Name.toString)}"
        IO.println s!"PATH_VISITED_COUNT={root}|{target}|{queue.size}"
      else
        match env.find? current with
        | none => IO.println s!"PATH_REACHED_DECLARATION_MISSING={current}"
        | some ci =>
          for dep in ci.getUsedConstantsAsSet do
            if !seen.contains dep then
              seen := seen.insert dep
              queue := queue.push (dep, dep :: path)
    if !found then
      IO.println s!"PATH_NOT_FOUND_COVERAGE_UNVERIFIED={root}|{target}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
