import AIM939_COUNTEREXAMPLE
import Lean.Util.CollectAxioms

/-!
Theorem-level transitive axiom audit.
Every target must be a theorem already imported from compiled proof modules.
Any axiom outside the three standard permitted names is a hard error.
-/

#check AIM939.exists_counterexample
#check AIM939.AIM939_COUNTEREXAMPLE
#print axioms AIM939.diagonal_concave
#print axioms AIM939.midpoint_violation
#print axioms AIM939.not_concaveOn_rootQuarter_f
#print axioms AIM939.exists_counterexample
#print axioms AIM939.AIM939_COUNTEREXAMPLE

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``AIM939.fOf_coefficients,
    ``AIM939.f_diagonal,
    ``AIM939.coefficients_pos,
    ``AIM939.diagonal_curvature_identity,
    ``AIM939.diagonal_concave,
    ``AIM939.qMinus_pow4_lt,
    ``AIM939.qMid_pow4_gt,
    ``AIM939.qPlus_pow4_lt,
    ``AIM939.midpoint_violation,
    ``AIM939.not_concaveOn_rootQuarter_f,
    ``AIM939.exists_counterexample,
    ``AIM939.AIM939_COUNTEREXAMPLE]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in targets do
    match (← getEnv).find? target with
    | some (.thmInfo _) => pure ()
    | _ => throwError "AUDIT_TARGET_IS_NOT_A_THEOREM: {target}"
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "UNAPPROVED_AXIOM: theorem={target}, axiom={axiomName}"
    logInfo m!"AXIOM_AUDIT_PASS={target}; AXIOMS={axioms}"
  logInfo "AIM939_THEOREM_AUDIT=PASS_STANDARD_ONLY"
