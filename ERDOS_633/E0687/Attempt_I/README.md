# Erdős #687 — Attempt_I (BKQR/Hankel finite-survivor reduction)

Toolchain: Lean 4.34.0-rc1, pinned Mathlib revision fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0.

## Exact endpoints

- Finite Hankel nonzero iff the survivor set is nonempty (for T > 0).
- Executable exhaustive gcd-based checker iff all residue classes contain a survivor.
- Maximal failed-length yMod equivalence with the checker.
- Finite-coordinate witness soundness/completeness.
- Prime-primorial version of those statements.
- Conditional asymptotic exponent implication, with the **uniform acceptance premise explicit**.

The exponent-bound premise is equivalent to the exponent target, **not a proof of Erdős #687**.

## Audit gate

CI compiles Erdos687.lean with cached dependencies and separately compiles Audit.lean.
The audit parser checks each named theorem and rejects any axiom outside
propext, Classical.choice, Quot.sound (including sorryAx).

A_TIER_CANDIDATE until a matching external CI PASS and theorem-level axiom audit.
No local Lean run is used. `run.cmd` is provided for optional native Windows cached replay.
