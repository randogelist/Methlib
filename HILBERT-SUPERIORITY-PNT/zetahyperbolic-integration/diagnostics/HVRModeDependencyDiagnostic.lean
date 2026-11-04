import HVR_PrimeDensity_FinalRoot
import HVR_PrimeMellin_Abel
import Mathlib.NumberTheory.LSeries.SumCoeff
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-!
Diagnostic only. Positive controls intentionally depend on the two central
targets and must never be imported by the PNT proof. Importing the existing
MellinCandidate module is not equivalent to using its Mellin theorem. A
negative traversal is not proof of semantic independence or trace coverage.
-/

open Lean Elab Command

namespace HVRModeTraceControl
def mellinDirect := @HVRPrimeCountMellin.primeSeries_eq_mul_primeThetaMellin
def mellinIndirect := mellinDirect
def modeDirect := @HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes
def modeIndirect := modeDirect
def targetDirect := @LSeries_eq_mul_integral
def targetIndirect := targetDirect
def primePowerDirect := @HVRSnditerationPrimePowerTail.higher_prime_power_hasSum
def primePowerIndirect := @primePowerDirect
def correctionDirect := @HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection
def correctionIndirect := correctionDirect
end HVRModeTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[
    (`HVRModeTraceControl.mellinDirect, `HVRPrimeCountMellin.primeSeries_eq_mul_primeThetaMellin),
    (`HVRModeTraceControl.mellinIndirect, `HVRPrimeCountMellin.primeSeries_eq_mul_primeThetaMellin),
    (`HVRModeTraceControl.modeDirect, `HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes),
    (`HVRModeTraceControl.modeIndirect, `HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes),
    (`HVRModeTraceControl.targetDirect, `LSeries_eq_mul_integral),
    (`HVRModeTraceControl.targetIndirect, `LSeries_eq_mul_integral),
    (`HVRModeTraceControl.primePowerDirect, `HVRSnditerationPrimePowerTail.higher_prime_power_hasSum),
    (`HVRModeTraceControl.primePowerIndirect, `HVRSnditerationPrimePowerTail.higher_prime_power_hasSum),
    (`HVRModeTraceControl.correctionDirect, `HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection),
    (`HVRModeTraceControl.correctionIndirect, `HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection)]
  for (root, target) in controls do
    if (env.find? root).isNone || (env.find? target).isNone then
      throwError "CONTROL_OR_TARGET_UNKNOWN={root}|{target}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if deps.contains target then
      IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
    else
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
  let roots : Array Name := #[
    `HVRPrimeCountGrowth.primeTheta_eq_chebyshev,
    `HVRPrimeCountLogSubstitution.primeThetaMellin_eq_exp_integral,
    `HVRPrimeMellinModeAssembly.theta_exp_laplace_unconditional,
    `HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes,
    `HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection,
    `HVRZetaCorrectionIdentity.zeta_log_deriv_eq_primeSeries_add_complexCorrection,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one]
  let targets : Array Name := #[
    `HVRPrimeCountMellin.primeSeries_eq_mul_primeThetaMellin,
    `HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes,
    `HVRPrimeMellinAbel.lseries_eq_mellin_of_zero,
    `HVRSnditerationPrimePowerTail.higher_prime_power_hasSum,
    `HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection,
    `HVRZetaCorrectionIdentity.zeta_log_deriv_eq_primeSeries_add_complexCorrection,
    `LSeries_eq_mul_integral,
    `HVRZetaLogDerivative.vonMangoldt_series_eq_zeta_log_deriv,
    `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div]
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
