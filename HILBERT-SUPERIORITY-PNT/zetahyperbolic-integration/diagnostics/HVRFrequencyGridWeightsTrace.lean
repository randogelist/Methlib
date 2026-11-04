import HVRFrequencyMeshLimit
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
Diagnostic for positive and negative reachability observations. This does not
replace theorem-level axiom checks, and a negative result is not a proof of
semantic independence. Controls are diagnostic-only.
-/

open Lean Elab Command

namespace HVRFrequencyGridWeightsTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRFrequencyGridWeightsTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  let controls : Array Name := #[
    `HVRFrequencyGridWeightsTraceControl.direct,
    `HVRFrequencyGridWeightsTraceControl.indirect]
  if (env.find? target).isNone then
    throwError "TARGET_UNKNOWN={target}"
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[
    `HVRFrequencyCellBudget.disjoint_cells_integral_norm_sum_le,
    `HVRFrequencyCellBudget.disjoint_cells_coefficient_norm_sum_le,
    `HVRFrequencyCellBudget.finite_cells_phase_error_of_disjoint,
    `HVRFrequencyWeightedCoefficients.norm_weightedFrequency,
    `HVRFrequencyWeightedCoefficients.weightedFrequency_integrable,
    `HVRFrequencyWeightedCoefficients.actual_coefficients_norm_sum_le,
    `HVRFrequencyIntervalCells.gridCells_pairwise_disjoint,
    `HVRFrequencyIntervalCells.gridCells_cover,
    `HVRFrequencyIntervalCells.gridCells_close_ae,
    `HVRFrequencyGridWeights.actual_grid_coefficients_norm_sum_le,
    `HVRFrequencyMeshLimit.grid_mesh_tendsto_zero,
    `HVRFrequencyMeshLimit.tendsto_of_grid_error]
  for root in roots do
    if (env.find? root).isNone then
      throwError "ROOT_UNKNOWN={root}"
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
        if ci.isTheorem && (ci.value? true).isNone then
          hidden := hidden + 1
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
