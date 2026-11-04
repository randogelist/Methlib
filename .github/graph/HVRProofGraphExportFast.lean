import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
import Lean.DeclarationRange

/-!
One-root proof constant census. Use HVR_GRAPH_ROOT=root, old_helper,
new_helper, correction, kernel, two_prime, mass, or assembly; default root.
For kernel, two_prime, mass, or assembly, add
`import HVRPrimeSndAssembly` to a copy before running it.
Redirected artifact: hvr-proof-graph.tsv in the Lean process working directory.
This diagnostic follows type + available value constants. It excludes tactic
and elaborator source dependencies; missing ranges or values limit coverage.
Use external cached Lean only. This candidate has not been locally compiled.
-/

open Lean Elab Command

namespace HVRGraphFastControls
def direct := @Nat.add_comm
def indirect := @direct
end HVRGraphFastControls

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for (source, target) in #[
      (`HVRGraphFastControls.direct, `Nat.add_comm),
      (`HVRGraphFastControls.indirect, `Nat.add_comm)] do
    let ds ← liftCoreM source.transitivelyUsedConstants
    unless ds.contains target do
      throwError "GRAPH_CONTROL_MISSED={source}|{target}"
    IO.println s!"GRAPH_CONTROL_PASS|{source}|{target}"
  let selection := (← IO.getEnv "HVR_GRAPH_ROOT").getD "root"
  let root : Name ← match selection with
    | "root" => pure `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one
    | "old_helper" => pure `HVRHigherCoefficientGeometric.correction_prime_power_tsum
    | "new_helper" => pure `HVRSnditerationPrimePowerTail.higher_prime_power_hasSum
    | "correction" => pure `HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection
    | "kernel" => pure `HVRPrimeKernelTrace.prime_gram_logDet_kernel_hasDerivAt
    | "two_prime" => pure `HVRTwoPrimeGram.gram_det_pos
    | "mass" => pure `HVRPrimeMomentDecay.log_mass_derivative_le_neg_log_two
    | "assembly" => pure `HVRPrimeSndAssembly.two_prime_logDet_kernel_hasDerivAt
    | _ => throwError "GRAPH_SELECTION_UNKNOWN={selection}"
  if (env.find? root).isNone then
    throwError "GRAPH_ROOT_ABSENT={root}"
  IO.println s!"GRAPH_START|{root}"
  let deps ← liftCoreM root.transitivelyUsedConstants
  IO.println s!"GRAPH_REACH_DONE|{root}"
  let mut rows : Array String := #[]
  let mut count : Nat := 0
  let mut missing : Nat := 0
  let mut hidden : Nat := 0
  let mut unknownModule : Nat := 0
  let mut missingRange : Nat := 0
  let mut axioms : Nat := 0
  for n in deps do
    count := count + 1
    if count % 2000 == 0 then
      IO.println s!"GRAPH_PROGRESS|{root}|{count}"
    match env.find? n with
    | none =>
      missing := missing + 1
      rows := rows.push s!"GRAPH_MISSING|{root}|{n}"
    | some ci =>
      let modName := (env.getModuleFor? n).getD `_unknown
      if modName == `_unknown then
        unknownModule := unknownModule + 1
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      if kind == "axiom" then
        axioms := axioms + 1
      if (kind == "theorem" || kind == "opaque") && (ci.value? true).isNone then
        hidden := hidden + 1
      let ranges ← liftCoreM (findDeclarationRanges? n)
      match ranges with
      | none =>
        missingRange := missingRange + 1
        rows := rows.push s!"GRAPH_CONST|{root}|{n}|{modName}|{kind}|0|0|0|0"
      | some ranges =>
        let r := ranges.range
        rows := rows.push s!"GRAPH_CONST|{root}|{n}|{modName}|{kind}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}"
  let summary := s!"GRAPH_SUMMARY|{root}|{count}|{missing}|{hidden}|{unknownModule}|{missingRange}|{axioms}"
  rows := rows.push summary
  IO.FS.writeFile "hvr-proof-graph.tsv" (String.intercalate "\n" rows.toList ++ "\n")
  IO.println summary
  IO.println "GRAPH_COVERAGE=NOT_YET_VALIDATED"
  IO.println "GRAPH_EXCLUDES_TACTIC_AND_ELABORATOR_SOURCE=YES"
  IO.println "GRAPH_FILE=hvr-proof-graph.tsv"
