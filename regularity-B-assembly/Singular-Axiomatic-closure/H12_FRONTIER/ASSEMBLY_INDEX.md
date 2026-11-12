# H12_FRONTIER: executed assembly

```text
BRANCH=H12_extension
CORE_MILESTONES_CLOSED=14/14
MILESTONE_MARKER=!=!
STATUS=UNCONDITIONAL_CLOSURE_CONCRETE_ADMISSIBLE_INSTANCE
COMPILED_SOURCE=d8b5e510411c224fd7b284b0a65eb2f9b08b3d83
EXTERNAL_CACHED_RUN=43317474994
BASE_REGRESSION=PASS
LOCAL_LEAN_EXECUTIONS=0
OPTIONAL_E15=OPEN
```

## Authoritative execution record

[Execution manifest](verification/frontier/EXECUTION.json) · [Core status](verification/frontier/CORE_STATUS.json) · [A-tier report](FRONTIER_H12_A_TIER.txt) · [Synchronized summary](FRONTIER_H12_ASSEMBLY_SUMMARY.txt).

All fourteen exact registered concrete endpoints compiled and passed their theorem-level axiom audits. The constructed conservative Sobolev constant instance is explicit in the source and in the execution report; no auxiliary nonlinear certificate remains assumed by either root. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

The native root is `SingularClosure.H12Frontier.FRONTIER_H12_NATIVE`; the coefficient-normalized public root is `SingularClosure.H12Frontier.FRONTIER_H12`.

## Dependency specifications and historical indexing

[index/ENDPOINTS.md](index/ENDPOINTS.md) retains the registered mathematical scopes. [index/INDEX.json](index/INDEX.json), the ten indexing rounds, and the native/Mathlib identity maps retain their source-pinned planning context. Their earlier `PLANNED` or `0/14` fields are historical, not the current completion ledger. Current execution status is exclusively the manifest above.

[Native identities](index/BASE_IDENTITIES.md) · [Pinned Mathlib identities](index/MATHLIB_IDENTITIES.md).

## Scope boundary

E15 remains open: no proof of `frontierConstant < criticalNonlinearConstant` is asserted. Consequently the completed concrete root is not claimed to strictly enlarge the original compiled Methlib ball. No optimal numerical or arbitrary prescribed literature constant is substituted for the actual proved instance.

The original base Lean sources remain unchanged; all 259 original base Lean hashes agree with the original manifest. The fresh external run also passes the base root's exact-type and standard-only axiom regression.
