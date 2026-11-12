# Round 08 — Deterministic Assembly Order

## Phase 0 — Frozen-source regression

```text
P0.1 hash copied base anchors
P0.2 build copied base package through cached Lean 4.33.0
P0.3 exact-type audit original root
P0.4 theorem-level axiom audit original root
```

No frontier theorem is compiled before the copied base is reproducible at its
new path.

## Phase 1 — Contract and scalar arithmetic

```text
P1.1 FrontierConstantData
P1.2 frontierNonlinearConstant
P1.3 positivity of sqrt 2
P1.4 positivity of frontierNonlinearConstant
P1.5 inverse/radius identity
P1.6 monotonicity lemmas for constant transport
```

This phase is independent of NSE analysis.

## Phase 2 — Constant reconciliation

```text
P2.1 define C_repo, C_pkg1, C_lit, C_frontier interfaces
P2.2 state exact comparison predicates
P2.3 prove only available algebraic implications
P2.4 classify alias/inclusion/strict-extension cases
```

No unproved comparison is inserted into a root theorem.

## Phase 3 — Frontier nonlinear estimate

```text
P3.1 reproduce the literature ODI normalization in exact repository variables
P3.2 identify the finite physical pairing used by criticalNonlinearPower
P3.3 prove the frontier coefficient estimate uniformly in cutoff
P3.4 audit the endpoint independently
```

This is the principal analytic phase.

## Phase 4 — Frontier invariant

```text
P4.1 frontier differential inequality
P4.2 instantiate CRITICAL_ENERGY_INVARIANT
P4.3 prove norm invariance
P4.4 prove uniform H^(3/2) dissipation
P4.5 prove sharp quartic budget
P4.6 prove datumwise AX6 budget
```

Prefer thin theorem bodies invoking existing parameterized kernels.

## Phase 5 — Time derivative and compactness inputs

```text
P5.1 frontier H^(-1/2) RHS pointwise bound
P5.2 frontier integrated time-derivative budget
P5.3 frontier budget nonnegativity
P5.4 instantiate global Galerkin compactness
```

## Phase 6 — Strong trace and positive-time flow

```text
P6.1 reuse global coefficient subsequence
P6.2 reuse Bochner representatives
P6.3 reuse strong H^(1/2) trace
P6.4 prove positive-time H2 seed from frontier budgets
P6.5 reuse all-order bootstrap
P6.6 reuse physical positive-time NSE realization
```

## Phase 7 — Quantitative global class

```text
P7.1 frontier quantitative regularity record
P7.2 global L² H^(3/2)
P7.3 global L² H^(-1/2)
P7.4 global quartic gradient budget
P7.5 global L⁴ L⁶ Serrin membership
```

## Phase 8 — Physical closure

```text
P8.1 physical Leray–Hopf membership
P8.2 weak–strong uniqueness
P8.3 exact frontier root
P8.4 closure import module
```

## Phase 9 — Inclusion lattice

```text
P9.1 relation to literal literature ball
P9.2 relation to copied repository ball
P9.3 strictness witness when constant inequality is strict
P9.4 status table separating proved and unresolved comparisons
```

## Phase 10 — External promotion

```text
P10.1 cached full build
P10.2 every required module audit
P10.3 exact root type check
P10.4 theorem-level axiom audit
P10.5 source-manifest lock
P10.6 final status manifest
```

## Scheduling policy

Theorems may elaborate asynchronously when dependency-safe. Promotion occurs
only after all pending bodies pass the external Lean kernel. Scheduling changes
may not alter theorem types, premises, constants, or endpoints.

## First implementation tranche

The first code tranche should contain only:

```text
H12Frontier/Contracts.lean
H12Frontier/LiteratureConstants.lean
H12Frontier/Normalization.lean
H12Frontier/ConstantComparison.lean
```

This tranche determines whether the next operation is an adapter or a fresh
parallel invariant spine before expensive analytic duplication begins.