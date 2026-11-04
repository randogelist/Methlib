import HVRPrimeGridSwapDirect
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
open Lean Elab Command
namespace HVRPrimeGridSwapDirectTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRPrimeGridSwapDirectTraceControl
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  for root in #[`HVRPrimeGridSwapDirectTraceControl.direct, `HVRPrimeGridSwapDirectTraceControl.indirect] do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  for root in #[`HVRPrimeGridSwapDirect.abel_smoothing_eq_frequency_integral_of_support_interval, `HVRPrimeGridSwapDirect.abel_smoothing_eq_frequency_integral_of_compact_support] do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then IO.println s!"TARGET_FOUND={root}|{target}"
    else IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci => if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
