import HVR_PrimeDensity_FinalRoot
import HVR_PrimeDensity_PNTConditional
import HVR_PrimeDensity_AbelGlueConditional
import ImportGraph.Imports.RequiredModules

/-!
Optional diagnostic only: declaration-name traversal is not a semantic
independence proof. The uncompiled root list is explicit, import/object provenance is
partial, and body availability must be checked. The negative control tests
one known deliberately injected dependency. The negative sentinels name two
project theta-ratio declarations; absence cannot rule out a different PNT
statement or a mathematically equivalent imported theorem. No Lean run was
performed locally.
-/

open Lean Elab Command

namespace HVRDependencyTraceControl

def deliberatelyInjectedMarker : Nat := 271

def negativeControlUsesMarker : Nat := deliberatelyInjectedMarker + 1

end HVRDependencyTraceControl

set_option maxHeartbeats 0 in
run_cmd do
  let roots : Array (Name × Array Name) := #[
    (`HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one, #[
      `HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_concentrated_smoothing,
      `HVRPrimeDensityFinalRoot.actual_prime_concentrated_smoothing]),
    (`HVRPrimeDensityFinalRoot.actual_prime_concentrated_smoothing, #[
      `HVRPhysicalKernelTailScaling.exists_concentrated_scaled_kernel,
      `HVRPrimeDensityDecompositionEndpoint.scaled_smoothing_limits_of_backward_decomposition,
      `HVRPrimeDensityFinalRoot.backwardDecomposition]),
    (`HVRPrimeDensityFinalRoot.backwardDecomposition, #[
      `HVRPrimeDensityBackwardDecomposition.backward_eq_halfLine_add_error]),
    (`HVRZetaZeroFreeBoundary.zeta_nonzero_on_one_line, #[
      `HVRZetaGramResidueConditional.nonvanishing_of_all_zeta_residues,
      `HVRPrimePoleMass.normalized_primeMass_pole_limit,
      `HVRPrimeInfinite.infinite_prime_gram_nonnegative]),
    (`HVRPrimeDensityBoundaryLink.primeDensityLaplace_eq_patchedShift, #[
      `HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt,
      `HVRSmoothingBoundaryExtension.exp_integral_sub_pole_eq_patchedShift]),
    (`HVRSmoothingBoundaryExtension.patchedShift_continuous_boundary, #[
      `HVRSmoothingBoundaryExtension.patchedShift_continuousAt_imaginary,
      `HVRZetaZeroFreeBoundary.zeta_nonzero_on_one_line]),
    (`HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_concentrated_smoothing, #[
      `HVRPrimeDensityConcentratedSqueeze.primeDensity_tendsto_of_concentrated_smoothing,
      `HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_density]),
    (`HVRPrimeDensityAbelGlueConditional.undamped_tendsto_zero_of_dominated, #[
      `HVRPrimeDensityAbelGlueConditional.undamped_eq_ordinaryBoundary_of_dominated,
      `HVRPrimeBoundaryOrdinaryFrequencyDecay.ordinaryBoundary_tendsto_zero])]
  let forbidden : Array Name := #[
    `HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_density,
    `HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_concentrated_smoothing]
  let externalPntSentinels : Array Name := #[
    Name.str (Name.str Name.anonymous "Apery") "theta_asymptotic",
    Name.str (Name.str (Name.str Name.anonymous "KTheta") "RC1PNT") "theta_asymptotic",
    Name.str (Name.str Name.anonymous "Apery") "prime_number_theorem"]
  let env ← getEnv
  IO.println "DIAGNOSTIC_ONLY=YES"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "SENTINEL_ABSENCE_IS_NOT_INDEPENDENCE=YES"
  let control ← liftCoreM
    (`HVRDependencyTraceControl.negativeControlUsesMarker).transitivelyUsedConstants
  if control.contains `HVRDependencyTraceControl.deliberatelyInjectedMarker then
    IO.println "NEGATIVE_CONTROL_INJECTED_DEPENDENCY=DETECTED"
  else
    IO.println "NEGATIVE_CONTROL_INJECTED_DEPENDENCY=NOT_DETECTED"
  for (root, sentinels) in roots do
    IO.println s!"ROOT_BEGIN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for sentinel in externalPntSentinels do
      match env.find? sentinel with
      | none => IO.println s!"EXTERNAL_PNT_SENTINEL_UNAVAILABLE={sentinel}"
      | some _ =>
        if deps.contains sentinel then
          IO.println s!"EXTERNAL_PNT_SENTINEL_PRESENT={sentinel}"
        else
          IO.println s!"EXTERNAL_PNT_SENTINEL_ABSENT={sentinel}"
    for sentinel in sentinels do
      if deps.contains sentinel then
        IO.println s!"SENTINEL_PRESENT={sentinel}"
      else
        IO.println s!"SENTINEL_MISSING={sentinel}"
    -- These selected exact names do not exhaust the possible circular inputs.
    -- The theta roots themselves and their direct transfers are deliberately excluded
    -- from this negative check because the root is expected to use them.
    if root != `HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_concentrated_smoothing &&
       root != `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one then
      for sentinel in forbidden do
        match env.find? sentinel with
        | none => IO.println s!"NEGATIVE_SENTINEL_UNAVAILABLE={sentinel}"
        | some _ =>
          if deps.contains sentinel then
            IO.println s!"NEGATIVE_SENTINEL_PRESENT={sentinel}"
          else
            IO.println s!"NEGATIVE_SENTINEL_ABSENT={sentinel}"
    IO.println "DECLARATIONS_BEGIN"
    for n in deps do
      match env.find? n with
      | none => IO.println s!"DECL={n}|KIND=MISSING"
      | some ci =>
        let kind := if ci.isAxiom then "AXIOM" else if ci.isTheorem then "THEOREM"
          else if ci.isDefinition then "DEFINITION" else "OTHER_OR_OPAQUE"
        let hasBody := (ci.value? true).isSome
        IO.println s!"DECL={n}|KIND={kind}|BODY_REPORTED={hasBody}"
    IO.println "DECLARATIONS_END"
    IO.println s!"ROOT_END={root}"
  IO.println "INDEPENDENCE=NOT_YET_VERIFIED"
