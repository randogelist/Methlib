import HVR_PrimeDensity_FinalRoot
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Diagnostic only: target import and controls are not proof dependencies.
Positive findings are checked; negative findings remain coverage-unverified.
-/
open Lean Elab Command

namespace HVRIntegratedFourierTraceControl
def direct := @Real.tendsto_integral_exp_smul_cocompact
def indirect := @direct
end HVRIntegratedFourierTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target : Name := `Real.tendsto_integral_exp_smul_cocompact
  let targetModule : Name := `Mathlib.Analysis.Fourier.RiemannLebesgueLemma
  let candidate : Name := `HVRActualBoundaryFourier.ordinaryBoundary_tendsto_zero
  let controls : Array Name := #[`HVRIntegratedFourierTraceControl.direct,
    `HVRIntegratedFourierTraceControl.indirect]
  let roots : Array Name := #[
    `HVRPrimeBoundaryFourierDecay.weightedBoundary_fourier_tendsto_zero,
    `HVRPrimeBoundaryOrdinaryFrequencyDecay.ordinaryBoundary_tendsto_zero,
    `HVRActualBoundaryFourier.ordinaryBoundary_tendsto_zero,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one]
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "FOURIER_POSITIVE_CONTROL_MISSED={root}"
    IO.println s!"FOURIER_POSITIVE_CONTROL_DETECTED={root}|{target}"
  for root in roots do
    if (env.find? root).isNone then
      throwError "FOURIER_ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"FOURIER_TARGET_FOUND={root}|{target}"
    else
      IO.println s!"FOURIER_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    if deps.contains candidate then
      IO.println s!"FOURIER_CANDIDATE_FOUND={root}|{candidate}"
    let mut hiddenTheorems : Nat := 0
    let mut missing : Nat := 0
    let mut targetModuleCount : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then
          hiddenTheorems := hiddenTheorems + 1
        if env.getModuleFor? n == some targetModule then
          targetModuleCount := targetModuleCount + 1
          IO.println s!"FOURIER_TARGET_MODULE_DECLARATION={root}|{n}"
    IO.println s!"FOURIER_REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hiddenTheorems}"
    IO.println s!"FOURIER_REACHED_DECLARATIONS_MISSING={root}|{missing}"
    IO.println s!"FOURIER_TARGET_MODULE_DECLARATIONS_COUNT={root}|{targetModuleCount}"
  IO.println "FOURIER_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "FOURIER_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
