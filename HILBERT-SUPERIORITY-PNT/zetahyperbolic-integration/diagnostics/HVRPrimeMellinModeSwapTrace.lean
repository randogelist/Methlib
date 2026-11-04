import HVR_PrimeMellin_Modes
import Mathlib.MeasureTheory.Integral.Prod
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
/-! Controlled mode dependency diagnostic; negative coverage is unverified. -/
open Lean Elab Command
namespace HVRPrimeMellinModeSwapTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRPrimeMellinModeSwapTraceControl
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  for root in #[`HVRPrimeMellinModeSwapTraceControl.direct, `HVRPrimeMellinModeSwapTraceControl.indirect] do
    let ds ← liftCoreM root.transitivelyUsedConstants
    unless ds.contains target do throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  for root in #[`HVRPrimeMellinModes.weighted_exponential_mode, `HVRPrimeMellinModes.primeMode_integral, `HVRPrimeMellinModes.primeMode_integrable, `HVRPrimeMellinModes.primeMode_integral_norm, `HVRPrimeMellinModes.theta_exp_laplace_of_prime_expansion] do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
    let ds ← liftCoreM root.transitivelyUsedConstants
    if ds.contains target then IO.println s!"TARGET_FOUND={root}|{target}"
    else IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in ds do
      match env.find? n with
      | none => missing := missing + 1
      | some ci => if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
