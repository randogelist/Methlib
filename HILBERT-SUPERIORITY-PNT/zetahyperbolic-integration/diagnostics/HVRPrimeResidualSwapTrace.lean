import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Diagnostic only: negative reachability is not semantic independence. -/
open Lean Elab Command
namespace HVRPrimeResidualSwapTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRPrimeResidualSwapTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  let controls : Array Name := #[
    `HVRPrimeResidualSwapTraceControl.direct,
    `HVRPrimeResidualSwapTraceControl.indirect]
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one,
    `HVRPrimeDensityBoundaryLink.primeDensityLaplace_eq_patchedShift,
    `HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt,
    `HVRPrimeDensityLaplace.primeDensity_integrable,
    `HVRPrimeDensityLaplace.primeMass_complex_integrable,
    `HVRPrimeCountExpGrowth.logPrimeMass_integrableOn_exp_neg_mul,
    `HVRComplexPoleLaplace.exponential_integrable]
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
