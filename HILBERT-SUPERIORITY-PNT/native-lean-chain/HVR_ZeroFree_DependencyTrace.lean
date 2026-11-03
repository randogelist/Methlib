import HVR_Zeta_ZeroFreeBoundary
import ImportGraph.Imports.RequiredModules

/-!
Candidate declaration-dependency trace for the already audited zero-free
boundary theorem. This is an inspection tool, not a mathematical proof or
a verdict that the dependency chain is independent of PNT. The name list
must be semantically reviewed and the availability of imported declaration
bodies verified. No Lean execution was performed in preparing this file.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let root : Name := `HVRZetaZeroFreeBoundary.zeta_nonzero_on_one_line
  let deps ← liftCoreM root.transitivelyUsedConstants
  let env ← getEnv
  let sentinels : Array Name := #[
    `HVRZetaGramResidueConditional.nonvanishing_of_all_zeta_residues,
    `HVRPrimePoleMass.normalized_primeMass_pole_limit,
    `HVRPrimeInfinite.infinite_prime_gram_nonnegative,
    `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div]
  IO.println s!"DEPENDENCY_ROOT={root}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  for sentinel in sentinels do
    if deps.contains sentinel then
      IO.println s!"SENTINEL_PRESENT={sentinel}"
    else
      IO.println s!"SENTINEL_MISSING={sentinel}"
  IO.println "DEPENDENCY_LIST_BEGIN"
  for n in deps do
    match env.find? n with
    | none => IO.println s!"DECL={n}|KIND=MISSING"
    | some ci =>
      let kind := if ci.isAxiom then "AXIOM" else if ci.isTheorem then "THEOREM"
        else if ci.isDefinition then "DEFINITION" else "OTHER_OR_OPAQUE"
      let hasBody := (ci.value? true).isSome
      IO.println s!"DECL={n}|KIND={kind}|BODY_REPORTED={hasBody}"
  IO.println "DEPENDENCY_LIST_END"
  IO.println "INDEPENDENCE=NOT_YET_VERIFIED"
