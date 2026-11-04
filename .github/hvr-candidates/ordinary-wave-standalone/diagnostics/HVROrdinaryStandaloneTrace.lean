import HVROrdinarySeedWaveStandalone
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.Convolution
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
open Lean Elab Command
namespace HVROrdinaryStandaloneTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def convolutionDirect := @Real.fourier_mul_convolution_eq
def convolutionIndirect := @convolutionDirect
end HVROrdinaryStandaloneTraceControl
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[(`HVROrdinaryStandaloneTraceControl.swapDirect, `MeasureTheory.integral_integral_swap), (`HVROrdinaryStandaloneTraceControl.swapIndirect, `MeasureTheory.integral_integral_swap), (`HVROrdinaryStandaloneTraceControl.convolutionDirect, `Real.fourier_mul_convolution_eq), (`HVROrdinaryStandaloneTraceControl.convolutionIndirect, `Real.fourier_mul_convolution_eq)]
  for (root, target) in controls do
    let ds ← liftCoreM root.transitivelyUsedConstants
    unless ds.contains target do throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[`HVROneDimensionalCompactDecay.phase_integral_mul_eq_neg_derivative_integral, `HVROneDimensionalCompactDecay.phase_integral_derivative_bound, `HVRAnalyticPhaseBasics.phase_symm, `HVRAnalyticPhaseBasics.phase_frequency_lipschitz, `HVRAnalyticPhaseBasics.phase_mul_integrable, `HVRAnalyticPhaseBasics.integral_phase_frequency_lipschitz, `HVROrdinarySeed.complexSeed_compact, `HVROrdinarySeed.complexSeed_smooth, `HVRStandaloneSeedIntervalDecay.seed_deriv_integrable, `HVRStandaloneSeedIntervalDecay.phase_hasDerivAt, `HVRStandaloneSeedIntervalDecay.seed_phase_first_derivative_bound, `HVROrdinarySeedWave.ordinaryWave_eq_fourierInv, `HVROrdinarySeedWave.seed_integrable, `HVROrdinarySeedWave.seed_first_moment_integrable, `HVROrdinarySeedWave.ordinaryWave_norm_le, `HVROrdinarySeedWave.ordinaryWave_continuous, `HVROrdinarySeedWave.ordinaryWave_first_derivative_bound, `HVROrdinarySeedWave.ordinaryWave_norm_sq_integrable, `HVROrdinarySeedWave.ordinaryWave, `HVROrdinarySeed.complexSeed]
  for root in roots do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
    let ds ← liftCoreM root.transitivelyUsedConstants
    for target in #[`MeasureTheory.integral_integral_swap, `Real.fourier_mul_convolution_eq] do
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
