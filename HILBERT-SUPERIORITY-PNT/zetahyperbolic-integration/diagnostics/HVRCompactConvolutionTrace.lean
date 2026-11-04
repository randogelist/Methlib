import HVRCompactCorrelationFourierSquare
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
    `HVRCompactCorrelationQuadrature.complexSeed_exists_lipschitz,
    `HVRCompactCorrelationQuadrature.complexCorrelation_eq_integral,
    `HVRCompactCorrelationQuadrature.complexSeed_zero_off_interval,
    `HVRCompactCorrelationQuadrature.complexCorrelation_grid_error_of_lipschitz,
    `HVRCompactCorrelationQuadrature.sample_abs_le_half_band,
    `HVRCompactCorrelationQuadrature.sampledCorrelation_zero_of_band,
    `HVRCompactCorrelationQuadrature.frequency_interval_error_of_lipschitz,
    `HVRCompactCorrelationQuadrature.sampled_frequency_integral_tendsto_interval,
    `HVRCompactCorrelationRegularity.seed_correlation_mode_integrable,
    `HVRCompactCorrelationRegularity.complexCorrelation_frequency_lipschitz,
    `HVRCompactCorrelationRegularity.complexCorrelation_continuous_direct,
    `HVRCompactCorrelationRegularity.complexCorrelation_integrable_direct,
    `HVRCompactCorrelationRegularity.sampledCorrelation_continuous,
    `HVRCompactCorrelationRegularity.sampledCorrelation_hasCompactSupport,
    `HVRCompactCorrelationRegularity.modulated_correlation_integrable,
    `HVRCompactCorrelationRegularity.modulated_sampledCorrelation_integrable,
    `HVRCompactCorrelationRegularity.sampled_frequency_integral_tendsto_interval_direct,
    `HVRCompactCorrelationRegularity.modulated_correlation_interval_eq_full,
    `HVRCompactCorrelationRegularity.modulated_sampled_interval_eq_full,
    `HVRCompactCorrelationRegularity.sampled_frequency_integral_tendsto_full,
    `HVRCompactSeedPhaseGrid.sampledPhase_tendsto,
    `HVRPhaseTranslationDirect.phase_add,
    `HVRPhaseTranslationDirect.translated_phase_integral,
    `HVRCompactCorrelationPhaseSum.complexSeed_even,
    `HVRCompactCorrelationPhaseSum.translated_seed_phase_integrable,
    `HVRCompactCorrelationPhaseSum.sampled_phase_integral_eq_product,
    `HVRCompactCorrelationPhaseSum.sampled_phase_integrals_tendsto_square,
    `HVRCompactCorrelationFourierSquare.correlation_phase_integral_eq_square,
    `HVRCompactCorrelationFourierSquare.fourierInv_eq_phase_integral,
    `HVRCompactCorrelationFourierSquare.wave_eq_fourierInv_seed,
    `HVRCompactCorrelationFourierSquare.fourierInv_correlation_eq_wave_sq_direct]
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
