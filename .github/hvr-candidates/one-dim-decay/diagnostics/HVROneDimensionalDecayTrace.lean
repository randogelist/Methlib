import HVROneDimensionalDecay
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.Convolution
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
/-! Controlled diagnostic only; absence does not establish independence. -/
open Lean Elab Command
namespace HVRDecayTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def convolutionDirect := @Real.fourier_mul_convolution_eq
def convolutionIndirect := @convolutionDirect
end HVRDecayTraceControl
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[(`HVRDecayTraceControl.swapDirect, `MeasureTheory.integral_integral_swap), (`HVRDecayTraceControl.swapIndirect, `MeasureTheory.integral_integral_swap), (`HVRDecayTraceControl.convolutionDirect, `Real.fourier_mul_convolution_eq), (`HVRDecayTraceControl.convolutionIndirect, `Real.fourier_mul_convolution_eq)]
  for (root, target) in controls do
    let ds ← liftCoreM root.transitivelyUsedConstants
    unless ds.contains target do throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  for root in #[`HVROneDimensionalDecay.phase_integral_mul_eq_neg_derivative_integral, `HVROneDimensionalDecay.phase_integral_derivative_bound, `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable] do
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
