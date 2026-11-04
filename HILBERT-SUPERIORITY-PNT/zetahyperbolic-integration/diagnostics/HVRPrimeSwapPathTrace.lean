import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules

/-!
Dependency diagnostic only. Breadth-first search over the direct constants that
Lean exposes from each declaration. A found path witnesses name reachability;
an absent path cannot establish semantic independence or complete coverage.
No local Lean compilation has been performed.
-/
open Lean Elab Command

namespace HVRPrimeSwapPathControl
def injected := @MeasureTheory.integral_integral_swap
def indirect := @injected
end HVRPrimeSwapPathControl

set_option maxHeartbeats 0 in
run_cmd do
  let target := `MeasureTheory.integral_integral_swap
  let roots : Array Name := #[
    `HVRPrimeSwapPathControl.indirect,
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one,
    `HVRPhysicalKernelSpectralIdentity.fourierInv_correlation_eq_rawKernel,
    `HVRSpectralCorrelationFourierSquare.fourierInv_correlation_eq_wave_sq,
    `HVRSpectralCorrelationRegularity.correlation_continuous,
    `HVRSpectralCorrelationRegularity.correlation_integrable,
    `Real.fourier_mul_convolution_eq,
    `HVRPrimeMellinModes.weighted_exponential_mode,
    `HVRPrimeMellinModes.primeMode_integral_norm,
    `HVRPrimeMellinModes.primeMode_integrable,
    `HVRPrimeDensityBoundaryLink.primeDensityLaplace_eq_patchedShift,
    `HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt,
    `HVRPrimeDensityLaplace.primeDensity_integrable]
  for root in roots do
    let mut queue : Array Name := #[root]
    let mut parents : NameMap Name := {}
    let mut head : Nat := 0
    let mut found := root == target
    while head < queue.size && !found do
      let current := queue[head]!
      head := head + 1
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
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
