# Erdős #687 — Attempt_E: exact prime-moment / Jacobsthal bridge

## Theorem scope

- `AttemptE.lean`: no-axiom finite polynomial-square identity, Boolean checker soundness,
  and a **conditional formal implication** from the exact `JacobsthalQuadratic` statement
  to vanishing of all finite covered-shift certificates above a length `m ≤ C · π(x)^2`.
- `ExternalRoot.lean`: imports the public upstream
  `OAI.Erdos970.Erdos970Final.erdos_970_quadratic` directly and discharges the
  quadratic premise, in a separate Lean 4.34.1 environment.
- The upstream target is the quadratic **partial** bound; neither file proves
  the full conjectured `Y(x) ≪ x^(1+o(1))`.
- The CRT equivalence from arbitrary residue assignments defining `Y(x)` to
  `CoveredBlock (primorial x) H` is a classical B-tier bridge, **not** included
  in the formally audited root.

## Version locking

- External source: [`openai/math`](https://github.com/openai/math), commit
  `4eaee87548250b2682affda7d05d947c05554bae`.
- Upstream file: `lean/OAI/NumberTheory/Jacobsthal/Conclusions/QuadraticBound.lean`.
- Upstream theorem: `OAI.Erdos970.Erdos970Final.erdos_970_quadratic`.
- External Lean compiler: `4.34.1`, pinned upstream Mathlib via its original Lake manifest.
- Independent core Lean compiler: `4.34.0-rc1`, Mathlib commit
  `fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0`.
- **No local Lean execution.** Only matching GitHub CI output may establish A_TIER.

## CI

Workflow: `.github/workflows/erdos687-attempt-e.yml`.
Two independent jobs: cached conditional core and pinned external imported-root build.
Each job captures source IDs, compiler evidence, full build logs, and an axiom audit.
An external theorem-level `sorryAx` or unapproved axiom is a hard failure.

## Status

A_TIER_CANDIDATE until matching complete external CI compiler/audit evidence.
FORMAL_CLOSURE applies to the explicitly scoped result only, never to the
unproved near-linear Erdős #687 exponent.