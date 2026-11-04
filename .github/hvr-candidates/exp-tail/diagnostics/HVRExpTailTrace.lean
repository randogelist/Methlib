import HVRExpIntegralGeneralDirect
import Mathlib.MeasureTheory.Integral.Prod
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
/-! Controlled dependency diagnostic; no semantic independence claimed. -/
open Lean Elab Command
namespace HVRExpTailTraceControls
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRExpTailTraceControls
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  for root in #[`HVRExpTailTraceControls.direct, `HVRExpTailTraceControls.indirect] do
    let ds ← liftCoreM root.transitivelyUsedConstants
    unless ds.contains target do throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  for root in #[`HVRExpIntegralGeneralDirect.complex_exponential_integrable_tail, `HVRExpIntegralGeneralDirect.complex_integrable_exp_mul_Ioi, `HVRExpIntegralGeneralDirect.complex_integral_exp_mul_Ioi, `HVRExpIntegralGeneralDirect.real_integral_exp_mul_Ioi, `integrableOn_exp_mul_complex_Ioi, `integral_exp_mul_complex_Ioi] do
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
