# H12_FRONTIER Assembly Index

```text
BRANCH=H12_extension
BASE_BRANCH=main
SEED_COMMIT=ec62560d1e0f362f35cca2efb68635ed78b888c2
MODE=ASSEMBLY_INDEX
LOCAL_LEAN_EXECUTION=NONE
PROMOTION_POLICY=EXTERNAL_CACHED_COMPILER_PLUS_THEOREM_LEVEL_AXIOM_AUDIT
```

This directory indexes the construction of `FRONTIER_H12` on top of the copied
unconditional periodic critical `H^(1/2)_{sigma,0}` package.

The frozen base theorem is

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

with exact smallness premise

```lean
criticalNonlinearConstant * ‖a‖ < ν
```

and status `!!!! UNCONDITIONAL_CLOSURE` at the original externally audited
source snapshot. The copied source is an immutable dependency of the frontier
assembly; copied historical evidence is not itself a fresh audit of the new
path.

## Index rounds

| Round | File | Scope |
|---:|---|---|
| 1 | `ROUND_01_BASELINE_LOCK.md` | certified root and immutable snapshot |
| 2 | `ROUND_02_PACKAGE_INVENTORY.md` | package, compiler, scheduler, audit inventory |
| 3 | `ROUND_03_PROOF_SPINE.md` | exact dependency spine to the physical root |
| 4 | `ROUND_04_CONSTANT_SEAM.md` | repository, literature, and frontier constants |
| 5 | `ROUND_05_REUSE_BOUNDARY.md` | reusable kernels versus constant-sensitive wrappers |
| 6 | `ROUND_06_EXTENSION_DAG.md` | proposed frontier module graph and theorem signatures |
| 7 | `ROUND_07_AUDIT_INTEGRATION.md` | separate cached build and theorem-audit surface |
| 8 | `ROUND_08_ASSEMBLY_ORDER.md` | deterministic implementation sequence |
| 9 | `ROUND_09_RISK_REGISTER.md` | status and soundness hazards |
| 10 | `ROUND_10_DECISION_GATE.md` | adapter/parallel-spine decision procedure |

Machine-readable summary: `INDEX.json`.

## Assembly law

```text
FROZEN_BASE
  -> EXPLICIT_CONSTANT_RECONCILIATION
  -> FRONTIER_NONLINEAR_BOUND
  -> PARAMETRIC_INVARIANT_INSTANTIATION
  -> FRONTIER_BUDGETS
  -> EXISTING_COMPACTNESS_TRACE_PHYSICAL_SPINE
  -> FRONTIER_ROOT
  -> EXTERNAL_CACHED_BUILD
  -> EXACT_TYPE_AND_AXIOM_AUDIT
```

No strict enlargement theorem is promoted until the constant comparison and
frontier nonlinear estimate have exact proved types.