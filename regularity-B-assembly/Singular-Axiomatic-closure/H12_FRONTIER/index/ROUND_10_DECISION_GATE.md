# Round 10 — Adapter / Parallel-Spine Decision Gate

## 1. Input quantities

```text
C_repo      := criticalNonlinearConstant
C_frontier  := K2 / sqrt 2
```

The first executable frontier tranche must determine which of the following
relations is actually provable in the repository normalization.

## 2. Gate A — Exact alias

Condition:

```text
C_frontier = C_repo
```

Action:

```text
construct a theorem-name adapter only
reuse NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL directly
retain identical quantitative budgets
record no strict set extension
```

Target:

```lean
NSE_H12_FRONTIER_EQ_BASE
```

## 3. Gate B — Frontier premise implies base premise

Condition:

```text
C_repo <= C_frontier
```

Action:

```text
prove smallness transport
invoke the existing unconditional root
record frontier ball as a subset of the compiled base ball
```

Target:

```lean
NSE_H12_FRONTIER_VIA_BASE
```

This is an adapter, not a strict enlargement.

## 4. Gate C — Genuine larger centered ball

Condition:

```text
C_frontier < C_repo
```

Action:

```text
do not invoke the base root
prove FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND
instantiate the parameterized invariant with C_frontier
construct frontier-specific budgets
reuse the constant-independent compactness/trace/physical spine
prove a new unconditional root
prove strict inclusion with an explicit nonzero datum witness
```

Targets:

```lean
NSE_H12_FRONTIER_UNCONDITIONAL
H12_FRONTIER_STRICTLY_EXTENDS_BASE
```

## 5. Gate D — No comparison theorem

Condition:

```text
no order relation between C_repo and C_frontier has been proved
```

Action:

```text
continue the frontier nonlinear estimate independently
prove the frontier physical root as a parallel sufficient condition
state no inclusion relation with the compiled base ball
```

Target status:

```text
parallel unconditional regularity ball
comparison lattice OPEN
```

## 6. Preferred initial strategy

The implementation shall begin in Gate D mode. This avoids assuming a
constant relation and permits both roots to coexist. After both constants are
formal objects, `ConstantComparison.lean` may promote the relation to Gate A,
B, or C.

## 7. Minimal first package

```text
H12Frontier/Contracts.lean
H12Frontier/LiteratureConstants.lean
H12Frontier/Normalization.lean
H12Frontier/ConstantComparison.lean
H12Frontier.lean
ci/frontier_modules.txt
ci/frontier_required_audits.json
ci/frontier_audits/Normalization.lean
ci/frontier_audits/Normalization.json
```

The first externally audited endpoint is scalar:

```lean
frontier_radius_eq_sqrtTwo_div
```

No physical root promotion is attached to this scalar endpoint.

## 8. Second package decision

After the scalar audit:

```text
if Gate A or B is proved:
  build a short root adapter;
else:
  build NonlinearBound -> Invariant -> Budgets.
```

## 9. Final status matrix

| Result | Physical root | Inclusion | Marker ceiling |
|---|---|---|---|
| scalar normalization only | absent | absent | `!!` for scalar theorem only |
| comparison-premise adapter | conditional | proved under premise | `!!!` |
| exact alias theorem | inherited | equality | `!!!!` after external audit |
| parallel unconditional frontier root | new | open | `!!!!` for root, no strictness claim |
| parallel root plus strict comparison | new | strict extension | `!!!!` |

## 10. Frozen decision

```text
CURRENT_MODE=GATE_D_PARALLEL_SAFE
NEXT_IMPLEMENTATION=SCALAR_CONSTANT_TRANCHE
STRICT_EXTENSION_STATUS=UNPROVED
BASE_ROOT_STATUS=!!!! UNCONDITIONAL_CLOSURE
```
