import HVRZetaComputationalEquality
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
import Mathlib.MeasureTheory.Integral.Prod

/-! Diagnostic: the equality statement itself names `riemannZeta`. Absence
results remain coverage-unverified and are not semantic independence. -/
noncomputable section
open Lean Elab Command
namespace HVRZetaEqualityTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def equalityDirect := @HVRZetaComputationalProjection.projectedZeta_eq_riemannZeta
def equalityIndirect := @equalityDirect
end HVRZetaEqualityTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let swap := `MeasureTheory.integral_integral_swap
  let equality := `HVRZetaComputationalProjection.projectedZeta_eq_riemannZeta
  let zeta := `riemannZeta
  let controls : Array (Name × Name) := #[
    (`HVRZetaEqualityTraceControl.swapDirect, swap),
    (`HVRZetaEqualityTraceControl.swapIndirect, swap),
    (`HVRZetaEqualityTraceControl.equalityDirect, equality),
    (`HVRZetaEqualityTraceControl.equalityIndirect, equality)]
  for (root, dest) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains dest do throwError "ZETA_EQ_CONTROL_MISSED={root}|{dest}"
    IO.println s!"ZETA_EQ_CONTROL_DETECTED={root}|{dest}"
  for root in #[`HVRZetaComputationalProjection.projectedZeta, equality, zeta] do
    if (env.find? root).isNone then throwError "ZETA_EQ_ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for dest in #[swap, zeta] do
      if deps.contains dest then
        IO.println s!"ZETA_EQ_TARGET_FOUND={root}|{dest}"
      else
        IO.println s!"ZETA_EQ_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{dest}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"ZETA_EQ_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"ZETA_EQ_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "ZETA_EQ_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "ZETA_EQ_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
