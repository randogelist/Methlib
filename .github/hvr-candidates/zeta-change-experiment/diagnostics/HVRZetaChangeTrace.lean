import HVRZetaChangeExperiment
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
import Mathlib.MeasureTheory.Integral.Prod

/-! Controlled syntactic dependency experiment, not semantic independence. -/
noncomputable section
open Lean Elab Command
namespace HVRZetaChangeTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def zetaDirect := @riemannZeta
def zetaIndirect := @zetaDirect
end HVRZetaChangeTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let swap := `MeasureTheory.integral_integral_swap
  let zeta := `riemannZeta
  let raw := `HVRZetaDefeqProjection.rawZeta
  let controls : Array (Name × Name) := #[
    (`HVRZetaChangeTraceControl.swapDirect, swap),
    (`HVRZetaChangeTraceControl.swapIndirect, swap),
    (`HVRZetaChangeTraceControl.zetaDirect, zeta),
    (`HVRZetaChangeTraceControl.zetaIndirect, zeta)]
  for (root, dest) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains dest do throwError "ZETA_CHANGE_CONTROL_MISSED={root}|{dest}"
    IO.println s!"ZETA_CHANGE_CONTROL_DETECTED={root}|{dest}"
  for root in #[`HVRZetaChangeExperiment.raw_reflexivity,
      `HVRZetaChangeExperiment.raw_statement_changed_to_zeta,
      `HVRZetaChangeExperiment.zeta_statement_changed_to_raw] do
    if (env.find? root).isNone then throwError "ZETA_CHANGE_ROOT_UNKNOWN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for dest in #[swap, zeta, raw] do
      if deps.contains dest then
        IO.println s!"ZETA_CHANGE_TARGET_FOUND={root}|{dest}"
      else
        IO.println s!"ZETA_CHANGE_TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{dest}"
    let mut hidden : Nat := 0
    let mut missing : Nat := 0
    for n in deps do
      match env.find? n with
      | none => missing := missing + 1
      | some ci =>
        if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"ZETA_CHANGE_THEOREM_BODIES_UNAVAILABLE={root}|{hidden}"
    IO.println s!"ZETA_CHANGE_DECLARATIONS_MISSING={root}|{missing}"
  IO.println "ZETA_CHANGE_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "ZETA_CHANGE_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"

#print HVRZetaChangeExperiment.raw_reflexivity
#print HVRZetaChangeExperiment.raw_statement_changed_to_zeta
#print HVRZetaChangeExperiment.zeta_statement_changed_to_raw
