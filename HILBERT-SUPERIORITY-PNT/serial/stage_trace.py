"""Generate the scoped Lean proof-dependency diagnostic; final proofs are imported objects."""
import re

LEAN_IDENT = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\Z")

# These modules are included in the pinned PNT dependency closure. The
# umbrella Mathlib.olean is optional in targeted Linux and Windows caches.
DIAGNOSTIC_IMPORTS = (
    'Mathlib.NumberTheory.Chebyshev',
    'Mathlib.NumberTheory.Harmonic.ZetaAsymp',
    'Mathlib.NumberTheory.LSeries.Dirichlet',
    'Mathlib.NumberTheory.EulerProduct.Basic',
    'Mathlib.Analysis.SpecificLimits.Normed',
    'Mathlib.MeasureTheory.Integral.DominatedConvergence',
    'Mathlib.MeasureTheory.Integral.Prod',
)

def diagnostic_imports(target):
    if target.startswith('MeasureTheory.'):
        return (DIAGNOSTIC_IMPORTS[6 if target == 'MeasureTheory.integral_integral_swap' else 5],)
    if target == 'hasSum_geometric_of_norm_lt_one':
        return (DIAGNOSTIC_IMPORTS[4],)
    if target == 'tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers':
        return (DIAGNOSTIC_IMPORTS[3],)
    if target.startswith(('primorial_', 'Nat.choose_', 'Chebyshev.')):
        return (DIAGNOSTIC_IMPORTS[0],)
    if 'LSeries' in target or target.startswith('ArithmeticFunction.'):
        return (DIAGNOSTIC_IMPORTS[2],)
    if 'riemannZeta' in target:
        return (DIAGNOSTIC_IMPORTS[1],)
    raise ValueError('diagnostic module missing for ' + target)

def lean_array(names):
    return '#['+', '.join('`'+n for n in names)+']'

def trace_lines(spec):
    target=spec['lean_target']
    callers=list(dict.fromkeys(e['caller'] for e in spec['edges']))
    proofs=spec.get('derivations',callers)
    reachable={e[k] for e in spec['edges'] for k in ('caller','helper')}
    if not proofs or not all(LEAN_IDENT.fullmatch(n) for n in [target,*callers,*proofs]):
        raise ValueError('invalid stage dependency names')
    if not set(proofs)<=reachable:
        raise ValueError('designated derivations must be on the audited caller/helper edges')
    return f'''
run_cmd do
  let env ← getEnv
  if (env.find? `{target}).isNone then throwError "TARGET_UNKNOWN={target}"

namespace HVRSerialAuditControl
noncomputable def directControl := @{target}
noncomputable def indirectControl := @directControl
end HVRSerialAuditControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `{target}
  let ctrl ← liftCoreM (getConstInfo `HVRSerialAuditControl.directControl)
  unless ctrl.getUsedConstantsAsSet.contains target do throwError "DIRECT_CONTROL_FAILED"
  let ctrlClosure ← liftCoreM (`HVRSerialAuditControl.indirectControl).transitivelyUsedConstants
  unless ctrlClosure.contains target do throwError "TRANSITIVE_CONTROL_FAILED"
  IO.println s!"POSITIVE_CONTROLS_DETECTED={{target}}"
  let explicit : Array Name := {lean_array(list(dict.fromkeys(callers+proofs)))}
  let actual : Array Name := {lean_array(proofs)}
  for n in explicit do
    let info ← liftCoreM (getConstInfo n)
    if (info.value? true).isNone then throwError "STAGE_BODY_UNAVAILABLE={{n}}"
    if info.getUsedConstantsAsSet.contains target then
      IO.println s!"DIRECT_TARGET_FOUND={{n}}|{{target}}"
      throwError "STAGE_DEFERRED_DIRECT_REUSE={{n}}|{{target}}"
    IO.println s!"DIRECT_TARGET_NOT_SEEN={{n}}|{{target}}"
  let mut complete := true
  for n in actual do
    let reached ← liftCoreM n.transitivelyUsedConstants
    let mut missing : Nat := 0
    let mut hidden : Nat := 0
    for d in reached do
      match env.find? d with
      | none => missing := missing + 1
      | some ci => if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
    IO.println s!"REACHED_DECLARATIONS_MISSING={{n}}|{{missing}}"
    IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={{n}}|{{hidden}}"
    if n == target || reached.contains target then
      complete := false
      IO.println s!"TARGET_FOUND={{n}}|{{target}}"
    else if missing != 0 || hidden != 0 then
      complete := false
      IO.println s!"TARGET_UNKNOWN_INCOMPLETE_COVERAGE={{n}}|{{target}}"
    else
      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={{n}}|{{target}}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  unless complete do throwError "STAGE_DEFERRED_TRANSITIVE_REUSE_OR_INCOMPLETE_COVERAGE"
  IO.println "SCOPED_EXCHANGE_TRACE=PASS"
'''.splitlines()
