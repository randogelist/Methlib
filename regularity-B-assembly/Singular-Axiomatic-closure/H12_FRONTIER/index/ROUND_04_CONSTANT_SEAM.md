# Round 04 — Constant Seam

## 1. Four distinct constants

The assembly currently contains four conceptually different coefficients.
They shall not be identified without an explicit theorem.

### Repository coefficient

```lean
C_repo := SingularClosure.criticalNonlinearConstant
```

Current unconditional root:

```text
C_repo * ‖a‖ < ν
```

### Earlier project B-tier coefficient

The earlier explicit derivation used

```text
C_pkg1 := 8 * C3^3
c_pkg1 := 1 / C_pkg1
```

with sufficient condition

```text
‖a‖ < c_pkg1 * ν.
```

### Literal literature coefficient

```text
C_lit := K2
ε_lit := 1 / K2
```

### Frozen frontier coefficient

```text
C_frontier := K2 / sqrt 2
ε_frontier := sqrt 2 / K2
```

The B-tier target `FRONTIER_H12` is

```text
C_frontier * ‖a‖ < ν -> global regularity.
```

## 2. Presently proved repository facts

```text
0 < C_repo
|criticalNonlinearPower| <= C_repo * sqrt(E1) * E3
C_repo * ‖a‖ < ν -> unconditional physical global root
```

`CriticalInvariant.lean` already proves the scalar invariant for an arbitrary
coefficient `C`, provided the corresponding differential inequality is
available.

## 3. Presently unproved identifications

No located Lean theorem currently proves any of:

```text
C_repo = K2
C_repo = K2 / sqrt 2
C_repo = 8 * C3^3
K2 = 8 * C3^3
C_frontier < C_repo
C_frontier <= C_repo
C_repo <= C_frontier
```

Consequently, the factor-sqrt-two B-tier sharpening is not automatically a
strict extension of the compiled repository ball.

## 4. Logical cases

### Case A — exact alias

If

```text
C_repo = C_frontier,
```

then `FRONTIER_H12` is an exact naming adapter over the existing unconditional
root. It is not a new Lean regularity region.

### Case B — transport to the base root

If

```text
C_repo <= C_frontier,
```

then

```text
C_frontier * ‖a‖ < ν
  -> C_repo * ‖a‖ < ν
  -> existing root.
```

This is a valid adapter but does not enlarge the current repository ball.

### Case C — genuine enlargement

If

```text
C_frontier < C_repo,
```

then the frontier condition is weaker and defines a larger centered ball.
The existing root cannot be invoked directly. A new proved estimate

```text
|criticalNonlinearPower 1 N c|
  <= C_frontier * sqrt(E1) * E3
```

must be supplied, followed by a new instantiation of the invariant and budget
spine.

## 5. Strictness certificate

A strict extension theorem requires both:

```text
0 < C_frontier
C_frontier < C_repo
```

and the frontier global root. Strict set inclusion then follows by choosing a
nonzero datum on a ray with norm between

```text
ν / C_repo
```

and

```text
ν / C_frontier.
```

The existence of a nonzero `CriticalSigmaZero` datum is a separate elementary
witness obligation.

## 6. First formal target

Before the physical extension root, formalize a constant ledger:

```lean
namespace SingularClosure.H12Frontier

structure ConstantLedger where
  K2 : ℝ
  K2_pos : 0 < K2

noncomputable def frontierNonlinearConstant
    (L : ConstantLedger) : ℝ := L.K2 / Real.sqrt 2

end SingularClosure.H12Frontier
```

This is data, not an analytic premise discharge.

## 7. Promotion boundary

The following are separate statuses:

```text
sqrt-two scalar arithmetic                    A_TIER target
literature proof-variable normalization       B_TIER source audit
frontier finite nonlinear estimate            OPEN Lean analytic edge
frontier physical root                         blocked on nonlinear estimate
strict inclusion over current Lean root        blocked on constant comparison
```

No status report may collapse these rows.