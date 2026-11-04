import HVR_PrimeDensity_FinalRoot
import NativeChebyshevBound
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
Diagnostic for the prime theta growth replacement. Positive controls are
deliberately kept outside all mathematical proof modules. These observations
do not establish completeness or semantic independence of a negative trace.
-/

open Lean Elab Command

namespace HVRChebyshevTraceControls
def targetDirect := @Chebyshev.theta_le_log4_mul_x
def targetIndirect := @targetDirect
def nativeDirect := @HVRNativeChebyshevBound.theta_le_log4_mul_x_native
def nativeIndirect := @nativeDirect
end HVRChebyshevTraceControls

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[
    (`HVRChebyshevTraceControls.targetDirect, `Chebyshev.theta_le_log4_mul_x),
    (`HVRChebyshevTraceControls.targetIndirect, `Chebyshev.theta_le_log4_mul_x),
    (`HVRChebyshevTraceControls.nativeDirect, `HVRNativeChebyshevBound.theta_le_log4_mul_x_native),
    (`HVRChebyshevTraceControls.nativeIndirect, `HVRNativeChebyshevBound.theta_le_log4_mul_x_native)]
  for (root, target) in controls do
    if (env.find? root).isNone || (env.find? target).isNone then
      throwError "CONTROL_OR_TARGET_UNKNOWN={root}|{target}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
    else
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
  let roots : Array Name := #[
    `HVRNativeChebyshevBound.primorial_lt_four_pow_native,
    `HVRNativeChebyshevBound.primorial_le_four_pow_native,
    `HVRNativeChebyshevBound.theta_le_log4_mul_x_native,
    `HVRPrimeCountGrowth.primeCoefficient_partial_sum_isBigO,
    `HVRPrimeLogDensity.logPrimeDensity_le_log_four,
    `HVRPrimeCountExpGrowth.logPrimeMass_isBigO_exp,
    `HVRPrimeCountExpGrowth.logPrimeMass_integrableOn_exp_neg_mul,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one]
  let targets : Array Name := #[
    `Chebyshev.theta_le_log4_mul_x,
    `primorial_lt_four_pow,
    `primorial_le_four_pow,
    `HVRNativeChebyshevBound.theta_le_log4_mul_x_native]
  for root in roots do
    if (env.find? root).isNone then
      throwError "ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for target in targets do
      if (env.find? target).isNone then
        throwError "TARGET_UNKNOWN={target}"
      if deps.contains target then
        IO.println s!"TARGET_FOUND={root}|{target}"
      else
        IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hiddenTheorems : Nat := 0
    let mut missingDecls : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missingDecls := missingDecls + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then
          hiddenTheorems := hiddenTheorems + 1
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hiddenTheorems}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missingDecls}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
