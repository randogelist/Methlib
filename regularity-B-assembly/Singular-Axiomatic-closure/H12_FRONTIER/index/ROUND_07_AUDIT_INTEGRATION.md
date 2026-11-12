# Round 07 — Audit and CI Integration

## 1. Preserve the base scheduler

The existing scheduler is locked to:

```python
ROOT_MODULE = "SingularClosure.SmallDataClosure"
ROOT_DECLARATION =
  "SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL"
```

It reads:

```text
ci/critical_modules.txt
ci/critical_required_audits.json
ci/critical_audits/
```

This surface shall continue to certify the copied base without frontier
modules.

## 2. Add a separate frontier scheduler

Proposed files:

```text
ci/frontier_modules.txt
ci/frontier_required_audits.json
ci/frontier_audits/
ci/build_frontier.py
ci/FrontierAudit.lean
ci/expected_frontier_axioms.json
run-frontier.cmd
```

Proposed scheduler constants:

```python
ROOT_MODULE = "SingularClosure.H12Frontier.Closure"
ROOT_DECLARATION =
  "SingularClosure.H12Frontier.NSE_H12_FRONTIER_UNCONDITIONAL"
BASE_ROOT_DECLARATION =
  "SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL"
```

## 3. Frontier required audits

Minimum required audit modules:

```text
SingularClosure.H12Frontier.Normalization
SingularClosure.H12Frontier.NonlinearBound
SingularClosure.H12Frontier.Invariant
SingularClosure.H12Frontier.Budgets
SingularClosure.H12Frontier.TimeDerivative
SingularClosure.H12Frontier.Compactness
SingularClosure.H12Frontier.PositiveTime
SingularClosure.H12Frontier.Quantitative
SingularClosure.H12Frontier.LerayHopf
SingularClosure.H12Frontier.Root
SingularClosure.H12Frontier.Closure
```

Audit basenames must be unique because the current scheduler maps a module to
its final path component.

## 4. Exact root audit

`ci/frontier_audits/Closure.lean` must contain:

```lean
import SingularClosure.H12Frontier.Closure

set_option autoImplicit false
set_option Elab.async false

example ... : <exact frontier root type> :=
  @SingularClosure.H12Frontier.NSE_H12_FRONTIER_UNCONDITIONAL ...

#eval IO.println
  "EXACT_TYPE_PASS:SingularClosure.H12Frontier.NSE_H12_FRONTIER_UNCONDITIONAL"
#check @SingularClosure.H12Frontier.NSE_H12_FRONTIER_UNCONDITIONAL
#print axioms SingularClosure.H12Frontier.NSE_H12_FRONTIER_UNCONDITIONAL
```

The companion JSON permits only:

```text
propext
Classical.choice
Quot.sound
```

and requires no custom axiom.

## 5. Base regression audit

The frontier runner must re-run the exact base audit before the frontier root
audit. Required result:

```text
BASE_ROOT_EXACT_TYPE=PASS
BASE_ROOT_AXIOMS=PASS_STANDARD_ONLY
```

## 6. Source-policy extension

The copied `check_sources.py` already rejects:

```text
sorry
admit
sorryAx
unapproved axiom declarations
```

Frontier sources are inside the same package root and are therefore covered by
the existing source walk. No exception shall be added for frontier contracts.

A certificate record is a theorem premise, not a Lean `axiom` declaration.
An unconditional root may not retain the certificate premise.

## 7. Cached runner order

`run-frontier.cmd` should execute:

```text
Lean 4.33.0 version lock
source-policy check
checker unit tests
base cached build and base audit
frontier module DAG build
frontier exact-type audits
frontier root axiom audit
status manifest generation
```

Use `lake exe cache get`; do not erase the existing Mathlib cache.

## 8. Evidence layout

```text
verification/frontier-<source-short-sha>/
├─ sources.json
├─ source-policy.json
├─ build-status.json
├─ base-root-build.log
├─ base-root-axioms.log
├─ frontier-root-build.log
├─ frontier-root-axioms.log
├─ audit.json
└─ final-run.json
```

## 9. Promotion law

```text
prepared source                        = A_TIER_CANDIDATE
matching external cached compile       = necessary
exact root type PASS                    = necessary
theorem-level PASS_STANDARD_ONLY        = necessary
no unresolved analytic premises         = necessary for !!!!
```

Copied historical evidence cannot promote modified frontier source.