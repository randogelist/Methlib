import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

elab "assert_standard_axioms " n:ident : command => do
  let decl ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms decl
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{decl} depends on unapproved axiom {ax}"
  logInfo m!"AXIOM_AUDIT_PASS=[{decl}]"
