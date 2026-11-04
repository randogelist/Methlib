import HVRPrimeLaplaceFrequencyConditional
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
    `HVRFrequencyTransformGrid.actual_prime_grid_cell_error,
    `HVRPrimeLaplaceFrequencyBounds.primeDensityLaplace_frequency_lipschitz,
    `HVRPrimeLaplaceFrequencyConditional.frequency_lipschitz_of_integrable_modes_moment,
    `HVRPrimeLaplaceFrequencyBounds.primeDensityLaplace_eq_damped_phase,
    `HVRPrimeLaplaceFrequencyBounds.actual_mixed_eq_damped_phase,
    `HVRZetaHyperbolicFrequencyBounds.integral_phase_frequency_lipschitz,
    `HVRPrimeWeightedMoment.dampedError_first_moment_integrable,
    `HVRZetaHyperbolicFiniteFrequency.actual_fixed_frequency_integrable,
    `HVRZetaHyperbolicFiniteFrequency.actual_fixed_frequency,
    `HVRNativeFubini.fixed_frequency_laplace,
    `HVRPrimeDensityLaplace.primeDensity_integrable,
    `HVRPrimeLogDensity.logPrimeDensity_le_log_four]
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
