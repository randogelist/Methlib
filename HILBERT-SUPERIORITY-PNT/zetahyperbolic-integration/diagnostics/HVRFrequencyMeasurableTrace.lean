import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Diagnostic only: negative traversal results have unverified coverage. -/
open Lean Elab Command
namespace HVRFrequencyMeasurableTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
def nativeDirect := @HVRPrimeBoundaryFrequencyMeasurable.frequencyIntegrand_aestronglyMeasurable
def nativeIndirect := @nativeDirect
end HVRFrequencyMeasurableTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let swap := `MeasureTheory.integral_integral_swap
  let native := `HVRPrimeBoundaryFrequencyMeasurable.frequencyIntegrand_aestronglyMeasurable
  let controls : Array (Name × Name) := #[
    (`HVRFrequencyMeasurableTraceControl.direct, swap),
    (`HVRFrequencyMeasurableTraceControl.indirect, swap),
    (`HVRFrequencyMeasurableTraceControl.nativeDirect, native),
    (`HVRFrequencyMeasurableTraceControl.nativeIndirect, native)]
  for (root, target) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "FREQ_MEAS_CONTROL_MISSED={root}|{target}"
    IO.println s!"FREQ_MEAS_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[
    `HVRPrimeBoundaryFrequencyMeasurable.primeDensity_frequency_continuous_native,
    native,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one]
  for root in roots do
    if (env.find? root).isNone then throwError "FREQ_MEAS_ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for target in #[swap, native] do
      if deps.contains target then
        IO.println s!"FREQ_MEAS_TARGET_FOUND={root}|{target}"
      else
        IO.println s!"FREQ_MEAS_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"FREQ_MEAS_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"FREQ_MEAS_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "FREQ_MEAS_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "FREQ_MEAS_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
