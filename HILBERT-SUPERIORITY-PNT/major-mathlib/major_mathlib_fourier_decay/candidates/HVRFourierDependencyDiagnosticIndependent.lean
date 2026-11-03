import HVRCompactFourierDecay
import HVRActualBoundaryFourier
import HVRFourierTraceControlBridge
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
Diagnostic only. The target module is imported here AFTER proof modules
were built, to expose its declarations to the trace; this import does not
change the already built proof objects. Trace control modules intentionally
use the target and must not be imported by production candidates. Negative
findings are not a semantic independence or complete proof-coverage claim.
-/
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target : Name := `Real.tendsto_integral_exp_smul_cocompact
  let targetModule : Name := `Mathlib.Analysis.Fourier.RiemannLebesgueLemma
  let controls : Array Name := #[`HVRFourierTraceControlLeaf.direct_target,
    `HVRFourierTraceControlBridge.indirect_target]
  let roots : Array Name := #[`HVRCompactFourierDecay.fourier_tendsto_atTop,
    `HVRCompactFourierDecay.fourier_tendsto_atBot,
    `HVRActualBoundaryFourier.weightedBoundary_fourier_tendsto_zero,
    `HVRActualBoundaryFourier.ordinaryBoundary_tendsto_zero]
  if (env.find? target).isNone then
    throwError "TARGET_UNKNOWN: diagnostic import did not load requested declaration"
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
    else
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
  for root in roots do
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"TARGET_FOUND={root}|{target}"
    else
      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hiddenTheorems : Nat := 0
    let mut sameModule : Nat := 0
    for n in deps do
      match env.find? n with
      | none => IO.println s!"REACHED_DECLARATION_MISSING={root}|{n}"
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then
          hiddenTheorems := hiddenTheorems + 1
        if env.getModuleFor? n == some targetModule then
          sameModule := sameModule + 1
          IO.println s!"TARGET_MODULE_DECLARATION={root}|{n}"
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hiddenTheorems}"
    IO.println s!"TARGET_MODULE_DECLARATIONS_COUNT={root}|{sameModule}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
