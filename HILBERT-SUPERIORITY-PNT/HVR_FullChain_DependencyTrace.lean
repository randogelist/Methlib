import HVR_PrimeDensity_BoundaryLink
import ImportGraph.Imports.RequiredModules

/-! Optional external diagnostic only. Its list must be semantically reviewed
alongside source provenance and imported proof-body coverage. Passing this
tool does not establish independence from PNT or a boundary zero-free theorem.
No local Lean execution was performed. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let roots : Array (Name × Array Name) := #[
    (`HVRZetaZeroFreeBoundary.zeta_nonzero_on_one_line, #[
      `HVRZetaGramResidueConditional.nonvanishing_of_all_zeta_residues,
      `HVRPrimePoleMass.normalized_primeMass_pole_limit,
      `HVRPrimeInfinite.infinite_prime_gram_nonnegative,
      `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div]),
    (`HVRPrimeDensityBoundaryLink.primeDensityLaplace_eq_patchedShift, #[
      `HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt,
      `HVRSmoothingBoundaryExtension.exp_integral_sub_pole_eq_patchedShift]),
    (`HVRSmoothingBoundaryExtension.patchedShift_continuous_boundary, #[
      `HVRSmoothingBoundaryExtension.patchedShift_continuousAt_imaginary,
      `HVRSmoothingAnalyticGerms.regularPartAt_differentiableAt_boundary,
      `HVRZetaZeroFreeBoundary.zeta_nonzero_on_one_line])]
  let env ← getEnv
  IO.println "DIAGNOSTIC_ONLY=YES"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  for (root, sentinels) in roots do
    IO.println s!"ROOT_BEGIN={root}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    for sentinel in sentinels do
      if deps.contains sentinel then
        IO.println s!"SENTINEL_PRESENT={sentinel}"
      else
        IO.println s!"SENTINEL_MISSING={sentinel}"
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
