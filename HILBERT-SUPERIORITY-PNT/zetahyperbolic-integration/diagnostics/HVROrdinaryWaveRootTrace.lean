import HVR_PrimeDensity_FinalRoot
import Mathlib.Analysis.Fourier.Convolution
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Positive-controlled dependency diagnostic: not a proof of complete
coverage or semantic independence. -/
open Lean Elab Command
namespace HVRCompactConvolutionTraceControls
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def convolutionDirect := @Real.fourier_mul_convolution_eq
def convolutionIndirect := @convolutionDirect
end HVRCompactConvolutionTraceControls
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[
    (`HVRCompactConvolutionTraceControls.swapDirect, `MeasureTheory.integral_integral_swap),
    (`HVRCompactConvolutionTraceControls.swapIndirect, `MeasureTheory.integral_integral_swap),
    (`HVRCompactConvolutionTraceControls.convolutionDirect, `Real.fourier_mul_convolution_eq),
    (`HVRCompactConvolutionTraceControls.convolutionIndirect, `Real.fourier_mul_convolution_eq)]
  for (root, target) in controls do
    unless (← liftCoreM root.transitivelyUsedConstants).contains target do
      throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let targets : Array Name := #[`MeasureTheory.integral_integral_swap, `Real.fourier_mul_convolution_eq]
  let roots : Array Name := #[
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one,
    `HVRPhysicalKernelSpectralIdentity.fourierInv_correlation_eq_rawKernel,
    `HVRPhysicalKernelCandidate.rawKernel,
    `HVRPhysicalKernelCandidate.rawKernel_continuous,
    `HVRPhysicalKernelCandidate.rawKernel_integrable,
    `HVRPhysicalKernelCandidate.mass_pos,
    `HVRPhysicalKernelWaveReal.ordinaryWave_im_zero,
    `HVROrdinarySeedWave.ordinaryWave,
    `HVROrdinarySeedWave.ordinaryWave_continuous,
    `HVROrdinarySeedWave.ordinaryWave_norm_sq_integrable,
    `HVRCompactCorrelationOrdinaryWave.fourierInv_correlation_eq_seed_transform_sq,
    `HVRPhysicalKernelCandidate.wave,
    `HVRCompactCorrelationFourierSquare.wave_eq_fourierInv_seed]
  for root in roots do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
    let ds ← liftCoreM root.transitivelyUsedConstants
    for target in targets do
      if ds.contains target then IO.println s!"TARGET_FOUND={root}|{target}"
      else IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in ds do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"REACHED_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
