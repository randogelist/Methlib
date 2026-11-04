import HVRZetaComputationalProjection
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
import Mathlib.MeasureTheory.Integral.Prod

/-! Controlled declaration-graph experiment. Unknown roots are reported and
skipped. Found paths witness syntactic reachability; absence is not a proof of
semantic independence or complete traversal coverage. -/
open Lean Elab Command
noncomputable section
namespace HVRZetaProjectionTraceControl
def swapDirect := @MeasureTheory.integral_integral_swap
def swapIndirect := @swapDirect
def projectedDirect := @HVRZetaComputationalProjection.projectedZeta
def projectedIndirect := @projectedDirect
end HVRZetaProjectionTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  let projected := `HVRZetaComputationalProjection.projectedZeta
  let controls : Array (Name × Name) := #[
    (`HVRZetaProjectionTraceControl.swapDirect, target),
    (`HVRZetaProjectionTraceControl.swapIndirect, target),
    (`HVRZetaProjectionTraceControl.projectedDirect, projected),
    (`HVRZetaProjectionTraceControl.projectedIndirect, projected)]
  for (root, dest) in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains dest do
      throwError "ZETA_PROJECTION_CONTROL_MISSED={root}|{dest}"
    IO.println s!"ZETA_PROJECTION_CONTROL_DETECTED={root}|{dest}"
  let roots : Array Name := #[
    `HVRZetaComputationalProjection.modifiedTheta,
    `HVRZetaComputationalProjection.projectedLambda,
    projected,
    `HurwitzZeta.evenKernel,
    `jacobiTheta₂,
    `Complex.Gammaℝ,
    `Complex.Gamma,
    `WeakFEPair.f_modif,
    `WeakFEPair.Λ,
    `riemannZeta]
  for root in roots do
    if (env.find? root).isNone then
      IO.println s!"ZETA_PROJECTION_ROOT_UNKNOWN={root}"
    else
      let mut queue : Array Name := #[root]
      let mut parents : NameMap Name := {}
      let mut head : Nat := 0
      let mut found := root == target
      let mut missing : Nat := 0
      let mut hidden : Nat := 0
      while head < queue.size && !found do
        let current := queue[head]!
        head := head + 1
        match env.find? current with
        | none => missing := missing + 1
        | some ci =>
          if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
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
          | none => throwError "ZETA_PROJECTION_PARENT_MISSING={root}|{current}"
          | some parent =>
            path := path.push parent
            current := parent
        IO.println s!"ZETA_PROJECTION_PATH_FOUND={root}|length={path.size}"
        for i in [:path.size] do
          IO.println s!"ZETA_PROJECTION_PATH_NODE={root}|{i}|{path[path.size - 1 - i]!}"
      else
        IO.println s!"ZETA_PROJECTION_NOT_SEEN_COVERAGE_UNVERIFIED={root}|visited={head}"
      IO.println s!"ZETA_PROJECTION_MISSING_DECLARATIONS={root}|{missing}"
      IO.println s!"ZETA_PROJECTION_UNAVAILABLE_THEOREM_BODIES={root}|{hidden}"
  IO.println "ZETA_PROJECTION_DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "ZETA_PROJECTION_SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
