import HVR_PrimeDensity_FinalRoot
import HVR_PrimeCount_GrowthCandidate
import HVR_PrimeMellin_Abel
import HVRMellinTraceControlBridge
import Mathlib.NumberTheory.LSeries.SumCoeff
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
DIAGNOSTIC ONLY. Build the actual root and the positive controls separately,
then compile this module. The diagnostic itself imports the target to ensure
the selected declaration is visible; this does not alter the compiled proofs.
The positive controls are deliberately target-dependent and must never be
imported by the PNT chain. A negative result only means the exact declaration
was not observed by this traversal, with coverage unverified. Import-module
and theorem-axiom checks are not equivalent to proof-dependency independence.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target : Name := `LSeries_eq_mul_integral
  let targetModule : Name := `Mathlib.NumberTheory.LSeries.SumCoeff
  let controls : Array Name := #[
    `HVRMellinTraceControlLeaf.direct_target,
    `HVRMellinTraceControlBridge.indirect_target]
  let roots : Array Name := #[
    `HVRPrimeMellinAbel.lseries_eq_mellin_of_zero,
    `HVRPrimeCountMellin.primeSeries_eq_mul_primeThetaMellin,
    `HVRPrimeCountMellin.zeta_log_deriv_eq_primeThetaMellin_add_correction,
    `HVRPrimeCountGrowth.primeSeries_eq_mul_primeThetaMellin_unconditional,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one]
  if (env.find? target).isNone then
    throwError "TARGET_UNKNOWN={target}"
  for root in controls do
    if (env.find? root).isNone then
      throwError "POSITIVE_CONTROL_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
    else
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
  for root in roots do
    if (env.find? root).isNone then
      throwError "ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"TARGET_FOUND={root}|{target}"
    else
      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hiddenTheorems : Nat := 0
    let mut missingDecls : Nat := 0
    let mut sameModule : Nat := 0
    for n in deps do
      match env.find? n with
      | none =>
        missingDecls := missingDecls + 1
        IO.println s!"REACHED_DECLARATION_MISSING={root}|{n}"
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then
          hiddenTheorems := hiddenTheorems + 1
        if env.getModuleFor? n == some targetModule then
          sameModule := sameModule + 1
          IO.println s!"TARGET_MODULE_DECLARATION={root}|{n}"
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hiddenTheorems}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missingDecls}"
    IO.println s!"TARGET_MODULE_DECLARATIONS_COUNT={root}|{sameModule}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
