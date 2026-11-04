import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Controlled dependency observations; negative coverage remains unverified. -/
open Lean Elab Command
namespace HVRComplexExpDirectTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def candidateDirect := @HVRComplexExpIntegralDirect.exponential_integrable_direct
def candidateIndirect := @candidateDirect
end HVRComplexExpDirectTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let swap := `MeasureTheory.integral_integral_swap
  let candidate := `HVRComplexExpIntegralDirect.exponential_integrable_direct
  let controls : Array (Name × Name) := #[
    (`HVRComplexExpDirectTraceControl.swapDirect, swap),
    (`HVRComplexExpDirectTraceControl.swapIndirect, swap),
    (`HVRComplexExpDirectTraceControl.candidateDirect, candidate),
    (`HVRComplexExpDirectTraceControl.candidateIndirect, candidate)]
  for (root, target) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "EXP_DIRECT_CONTROL_MISSED={root}|{target}"
    IO.println s!"EXP_DIRECT_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[
    `HVRComplexExpIntegralDirect.exponential_integrable_direct,
    `HVRComplexExpIntegralDirect.exponential_integral_eq_inv_direct,
    `HVRComplexPoleLaplace.exponential_integrable,
    `HVRComplexPoleLaplace.exponential_integral_eq_inv,
    `HVRPrimeDensityLaplace.primeDensity_integrable,
    `HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one]
  let targets : Array Name := #[swap, candidate,
    `integrableOn_exp_mul_complex_Ioi, `integral_exp_mul_complex_Ioi]
  for root in roots do
    if (env.find? root).isNone then throwError "EXP_DIRECT_ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for target in targets do
      if (env.find? target).isNone then throwError "EXP_DIRECT_TARGET_UNKNOWN={target}"
      if deps.contains target then
        IO.println s!"EXP_DIRECT_TARGET_FOUND={root}|{target}"
      else
        IO.println s!"EXP_DIRECT_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"EXP_DIRECT_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"EXP_DIRECT_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "EXP_DIRECT_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "EXP_DIRECT_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
