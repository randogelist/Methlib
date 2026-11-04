import HVR_PrimeDensity_FinalRoot
import Mathlib.Analysis.Fourier.Convolution
import ImportGraph.Imports.RequiredModules

/-! Diagnostic only. Positive paths establish declaration-name reachability;
negative observations do not establish complete coverage or independence. -/
noncomputable section
open Lean Elab Command

namespace HVRPrimeSwapPathControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def convolutionDirect := @Real.fourier_mul_convolution_eq
def convolutionIndirect := @convolutionDirect
end HVRPrimeSwapPathControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[
    (`HVRPrimeSwapPathControl.swapDirect, `MeasureTheory.integral_integral_swap),
    (`HVRPrimeSwapPathControl.swapIndirect, `MeasureTheory.integral_integral_swap),
    (`HVRPrimeSwapPathControl.convolutionDirect, `Real.fourier_mul_convolution_eq),
    (`HVRPrimeSwapPathControl.convolutionIndirect, `Real.fourier_mul_convolution_eq)]
  for (origin, dest) in controls do
    if (env.find? origin).isNone || (env.find? dest).isNone then
      throwError "PATH_CONTROL_UNKNOWN={origin}|{dest}"
    let ds ← liftCoreM origin.transitivelyUsedConstants
    if !ds.contains dest then throwError "PATH_CONTROL_MISSED={origin}|{dest}"
    IO.println s!"PATH_CONTROL_DETECTED={origin}|{dest}"
  let roots : Array Name := #[
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one,
    `HVRPhysicalKernelSpectralIdentity.fourierInv_correlation_eq_rawKernel,
    `HVROrdinarySeedWave.ordinaryWave,
    `HVRCompactCorrelationOrdinaryWave.fourierInv_correlation_eq_seed_transform_sq,
    `HVRSpectralCorrelationFourierSquare.fourierInv_correlation_eq_wave_sq,
    `HVRSpectralCorrelationRegularity.correlation_continuous,
    `HVRSpectralCorrelationRegularity.correlation_integrable,
    `HVRPrimeMellinModes.weighted_exponential_mode,
    `HVRPrimeMellinModes.primeMode_integral_norm,
    `HVRPrimeMellinModes.primeMode_integrable,
    `HVRPrimeDensityBoundaryLink.primeDensityLaplace_eq_patchedShift,
    `HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt,
    `HVRPrimeDensityLaplace.primeDensity_integrable]
  let targets : Array Name := #[`MeasureTheory.integral_integral_swap,
    `Real.fourier_mul_convolution_eq]
  for root in roots do
    if (env.find? root).isNone then
      IO.println s!"PATH_ROOT_UNKNOWN={root}"
    else
      let ds ← liftCoreM root.transitivelyUsedConstants
      for target in targets do
        if ds.contains target then
          IO.println s!"PATH_TARGET_FOUND={root}|{target}"
        else
          IO.println s!"PATH_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{target}"
      let mut hidden : Nat := 0
      let mut missing : Nat := 0
      for n in ds do
        match env.find? n with
        | none => missing := missing + 1
        | some ci =>
          if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
      IO.println s!"PATH_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
      IO.println s!"PATH_DECLARATIONS_MISSING={root}|{missing}"
  let target := `MeasureTheory.integral_integral_swap
  let root := `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one
  let mut queue : Array Name := #[root]
  let mut parents : NameMap Name := {}
  let mut head : Nat := 0
  let mut found := root == target
  let mut bfsMissing : Nat := 0
  while head < queue.size && !found do
    let current := queue[head]!
    head := head + 1
    if (env.find? current).isNone then
      bfsMissing := bfsMissing + 1
    else
      let ci ← liftCoreM (getConstInfo current)
      for next in ci.getUsedConstantsAsSet do
        if next != root && !(parents.contains next) then
          parents := parents.insert next current
          queue := queue.push next
          if next == target then found := true
  if found then
    let mut path : Array Name := #[target]
    let mut current := target
    while current != root do
      match parents.find? current with
      | none => throwError "SWAP_PATH_PARENT_MISSING={root}|{current}"
      | some parent =>
        path := path.push parent
        current := parent
    IO.println s!"SWAP_PATH_FOUND={root}|length={path.size}"
    for i in [:path.size] do
      IO.println s!"SWAP_PATH_NODE={root}|{i}|{path[path.size - 1 - i]!}"
  else
    IO.println s!"SWAP_PATH_NOT_SEEN_COVERAGE_UNVERIFIED={root}|visited={head}"
  IO.println s!"SWAP_PATH_BFS_MISSING={root}|{bfsMissing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
