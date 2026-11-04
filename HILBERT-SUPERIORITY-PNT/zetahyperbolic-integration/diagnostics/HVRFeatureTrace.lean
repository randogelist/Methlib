import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! External positive-control dependency diagnostic. Negative observations do
not establish complete dependency coverage or semantic independence. -/
open Lean Elab Command
namespace HVRFeatureTraceControl
def candidateDirect := @HVRNativeZetaPoleLittleO.zeta_log_derivative_regularized_isLittleO
def candidateIndirect := @candidateDirect
def targetDirect := @log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
def targetIndirect := @targetDirect
end HVRFeatureTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[
    (`HVRFeatureTraceControl.candidateDirect, `HVRNativeZetaPoleLittleO.zeta_log_derivative_regularized_isLittleO),
    (`HVRFeatureTraceControl.candidateIndirect, `HVRNativeZetaPoleLittleO.zeta_log_derivative_regularized_isLittleO),
    (`HVRFeatureTraceControl.targetDirect, `log_deriv_riemannZeta_add_inv_sub_sub_isLittleO),
    (`HVRFeatureTraceControl.targetIndirect, `log_deriv_riemannZeta_add_inv_sub_sub_isLittleO)]
  for (origin, dest) in controls do
    if (env.find? origin).isNone || (env.find? dest).isNone then
      throwError "FEATURE_CONTROL_UNKNOWN={origin}|{dest}"
    let ds ← liftCoreM origin.transitivelyUsedConstants
    if !ds.contains dest then
      throwError "FEATURE_CONTROL_MISSED={origin}|{dest}"
    IO.println s!"FEATURE_CONTROL_DETECTED={origin}|{dest}"
  let roots : Array Name := #[`HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one, `HVRNativeZetaPoleLittleO.zeta_log_derivative_regularized_isLittleO]
  let targets : Array Name := #[`HVRNativeZetaPoleLittleO.zeta_log_derivative_regularized_isLittleO, `log_deriv_riemannZeta_add_inv_sub_sub_isLittleO]
  for origin in roots do
    if (env.find? origin).isNone then throwError "FEATURE_ROOT_UNKNOWN={origin}"
    let ds ← liftCoreM origin.transitivelyUsedConstants
    for dest in targets do
      if ds.contains dest then
        IO.println s!"FEATURE_FOUND={origin}|{dest}"
      else
        IO.println s!"FEATURE_NOT_SEEN_COVERAGE_UNVERIFIED={origin}|{dest}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in ds do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"FEATURE_REACHED_THEOREM_BODIES_UNAVAILABLE={origin}|{hidden}"
    IO.println s!"FEATURE_REACHED_DECLARATIONS_MISSING={origin}|{missing}"
  IO.println "FEATURE_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "FEATURE_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
