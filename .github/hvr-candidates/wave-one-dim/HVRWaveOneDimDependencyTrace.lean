import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import ImportGraph.Imports.RequiredModules

/-! Diagnostic only; no negative observation establishes independence. -/
open Lean Elab Command
namespace HVRWaveOneDimDependencyTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRWaveOneDimDependencyTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  let controls : Array Name := #[
    `HVRWaveOneDimDependencyTraceControl.direct,
    `HVRWaveOneDimDependencyTraceControl.indirect]
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[
    `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable,
    `Real.fourier_deriv,
    `Real.hasDerivAt_fourierChar,
    `VectorFourier.fourierIntegral_fderiv,
    `intervalIntegral.integral_mul_deriv_eq_deriv_mul,
    `intervalIntegral.integral_deriv_mul_eq_sub,
    `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt,
    `intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt,
    `intervalIntegral.integral_eq_sub_of_hasDerivAt,
    `MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero,
    `Continuous.integrable_of_hasCompactSupport,
    `HasCompactSupport.deriv,
    `integrable_inv_one_add_sq]
  for root in roots do
    if (env.find? root).isNone then
      IO.println s!"ROOT_UNKNOWN={root}"
    else
      let deps ← liftCoreM root.transitivelyUsedConstants
      if deps.contains target then
        IO.println s!"TARGET_FOUND={root}|{target}"
      else
        IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
      let mut hidden : Nat := 0
      let mut missing : Nat := 0
      for n in deps do
        match env.find? n with
        | none => missing := missing + 1
        | some ci =>
          if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
      IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
      IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
