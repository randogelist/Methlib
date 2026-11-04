import HVRPrimeLeftFull
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
    `HVRPrimeLeftQuadrature.phase_mul_integrable,
    `HVRPrimeLeftQuadrature.gridCells_eq_Ioc,
    `HVRPrimeLeftQuadrature.intervalKernel_sample_error,
    `HVRPrimeLeftQuadrature.left_integral_error,
    `HVRPrimeLeftQuadrature.left_integrals_tendsto,
    `HVRPrimeLeftIntegrable.sample_outer_integrable,
    `HVRPrimeLeftIntegrable.phase_symm,
    `HVRPrimeLeftIntegrable.intervalKernel_norm_le,
    `HVRPrimeLeftIntegrable.weighted_frequency_moment_integrable,
    `HVRPrimeLeftIntegrable.intervalKernel_continuous,
    `HVRPrimeLeftIntegrable.interval_outer_integrable,
    `HVRPrimeLeftIntegrable.left_integrals_tendsto_direct,
    `HVRPrimeLeftFull.weighted_phase_eq_kernel_integrand,
    `HVRPrimeLeftFull.intervalKernel_eq_full_kernel,
    `HVRPrimeLeftFull.left_integrals_tendsto_actual_kernel,
    `HVRPrimeLeftFull.sampleKernel_mul_eq_weighted_modes,
    `HVRPrimeLeftFull.left_weighted_modes_tendsto_actual_kernel,
    `HVRPrimeLaplaceFrequencyBounds.primeDensityLaplace_frequency_lipschitz]
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
