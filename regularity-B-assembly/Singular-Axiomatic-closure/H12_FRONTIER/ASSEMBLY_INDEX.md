# H12_FRONTIER: canonical assembly organization

```text
BRANCH=H12_extension
ORGANIZATION_VERSION=2
CORE_MILESTONES=14
REPLAY_MILESTONES=9
OPTIONAL_COMPARISON_MILESTONES=1
IMPLEMENTATION_STATUS=PLANNED
LOCAL_LEAN_EXECUTIONS=0
NEW_THEOREM_PROMOTIONS=0
```

Authoritative assembly specification: [index/ENDPOINTS.md](index/ENDPOINTS.md).
Machine-readable dependency register: [index/INDEX.json](index/INDEX.json).
Historical indexing rounds and provenance: [index/README.md](index/README.md).

## Scope

Preserve the centered periodic, unforced, mean-zero, divergence-free H^(1/2)
criterion. This assembly is the FRONTIER_H12 constant adapter, not the separate
BMO/Beltrami/a_dagger perturbation program.

```text
E01-E02  norm and constant normalization
E03      explicit frontier nonlinear estimate
E04-E12  nine constant-dependent replay endpoints
E13      native quantitative physical root
E14      literature-normalized FRONTIER_H12
E15      optional comparison with the compiled repository constant
```

Fourteen is the selected number of top-level core milestones. It is not a
claim that fourteen Lean declarations suffice. Helper proofs, concrete
Sobolev-constant certificates, compactness/trace adapters, and exact-type/axiom
audits remain explicit work in the dependency register.

## Immutable base

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

Premise: `criticalNonlinearConstant * norm(a) < nu`.
Original externally audited source: `09dfe94a1ef150e21d09df3013fbe09002ef139c`.
Recorded original status: `!!!! UNCONDITIONAL_CLOSURE`.
The original package and the copied base Lean sources remain unchanged.
Historical evidence is not a fresh compilation at the copied path.

## Assembly rule

```text
NORM_LOCK -> CONSTANT_LOCK -> NONLINEAR_CERTIFICATE
  -> INVARIANT + DISSIPATION + QUARTIC + TIME_DERIVATIVE
  -> COMPACTNESS + REPRESENTATIVES + STRONG_TRACE
  -> POSITIVE_TIME_FLOW + PHYSICAL_QUANTITATIVE_TRANSFER
  -> NATIVE_ROOT -> FRONTIER_H12
```

E15 is independent of root completion. No strict enlargement of the compiled
base ball is asserted without its constant comparison and an explicit
admissible strict-inclusion witness. Definitions and source preparation alone
do not establish A_TIER.
