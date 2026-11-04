import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
import Lean.DeclarationRange

/-!
Proof-constant graph census. Execute only in an external cached environment.
Graph membership records are positive observations, not a completeness claim.
Constants referenced by theorem types and available values are both followed.
Tactics and elaborator source dependencies are not captured by this census.
-/

open Lean Elab Command

namespace HVRGraphExportControls
def direct := @Nat.add_comm
def indirect := @direct
end HVRGraphExportControls

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let controls : Array (Name × Name) := #[
    (`HVRGraphExportControls.direct, `Nat.add_comm),
    (`HVRGraphExportControls.indirect, `Nat.add_comm)]
  for (root, target) in controls do
    if (env.find? root).isNone || (env.find? target).isNone then
      throwError "GRAPH_CONTROL_UNKNOWN={root}|{target}"
    let deps ← liftCoreM root.transitivelyUsedConstants
    if !deps.contains target then
      throwError "GRAPH_CONTROL_MISSED={root}|{target}"
    IO.println s!"GRAPH_CONTROL_PASS|{root}|{target}"
  let roots : Array Name := #[
    `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one,
    `HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection,
    `HVRHigherCoefficientGeometric.correction_prime_power_tsum,
    `HVRSnditerationPrimePowerTail.higher_prime_power_hasSum]
  for root in roots do
    if (env.find? root).isNone then
      IO.println s!"GRAPH_ROOT_ABSENT|{root}"
    else
      let deps ← liftCoreM root.transitivelyUsedConstants
      let mut count : Nat := 0
      let mut missing : Nat := 0
      let mut hidden : Nat := 0
      let mut unknownModule : Nat := 0
      let mut missingRange : Nat := 0
      let mut axioms : Nat := 0
      for n in deps do
        count := count + 1
        match env.find? n with
        | none =>
          missing := missing + 1
          IO.println s!"GRAPH_MISSING|{root}|{n}"
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
            IO.println s!"GRAPH_CONST|{root}|{n}|{modName}|{kind}|0|0|0|0"
          | some ranges =>
            let r := ranges.range
            IO.println s!"GRAPH_CONST|{root}|{n}|{modName}|{kind}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}"
      IO.println s!"GRAPH_SUMMARY|{root}|{count}|{missing}|{hidden}|{unknownModule}|{missingRange}|{axioms}"
  IO.println "GRAPH_COVERAGE=NOT_YET_VALIDATED"
  IO.println "GRAPH_EXCLUDES_TACTIC_AND_ELABORATOR_SOURCE=YES"
