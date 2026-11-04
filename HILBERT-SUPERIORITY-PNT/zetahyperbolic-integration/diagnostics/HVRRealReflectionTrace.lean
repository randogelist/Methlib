import HVR_PrimeDensity_BackwardDecomposition
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

/-! Coverage-limited trace for the one-dimensional real reflection candidate. -/
open Lean Elab Command
namespace HVRRealReflectionTraceControl
def direct := @MeasureTheory.integral_integral_swap
def indirect := @direct
end HVRRealReflectionTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  let controls : Array Name := #[`HVRRealReflectionTraceControl.direct,
    `HVRRealReflectionTraceControl.indirect]
  for root in controls do
    let deps ← liftCoreM root.transitivelyUsedConstants
    unless deps.contains target do throwError "POSITIVE_CONTROL_MISSED={root}|{target}"
    IO.println s!"POSITIVE_CONTROL_DETECTED={root}|{target}"
  let roots : Array Name := #[`Real.map_volume_mul_left,
    `HVRRealReflection.neg_measurePreserving,
    `HVRRealReflection.real_volume_negInvariant_direct,
    `HVRRealReflection.subLeft_measurePreserving,
    `HVRRealReflection.subLeft_measurableEmbedding,
    `HVRRealReflection.integrable_subLeft,
    `HVRRealReflection.integral_subLeft,
    `HVRRealReflection.integrable_neg,
    `HVRPrimeDensityBackwardDecomposition.backward_eq_halfLine_add_error,
    `HVRPrimeDensityBackwardDecomposition.forward_eq_halfLine_add_reflected_error]
  for root in roots do
    if (env.find? root).isNone then throwError "ROOT_UNKNOWN={root}"
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
  IO.println "SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED"
