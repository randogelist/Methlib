# Erdős #687 — Attempt_F: BKQR dispersion + pinned Jacobsthal theorem

**State:** A_TIER_CANDIDATE. No matching CI compiler / theorem-level audit report accepted yet.

**Files**: `FiniteCore.lean`, `ExternalRoot.lean`, `Audit.lean`, `ci/run.sh`, `run.cmd`, `ERDOS_687_ATTEMPT_F_A_TIER.txt`.

## Exact scoped theorem

For `P q y : ℕ`, `Delta(P,q,y,t)` counts ordered pairs of P-sieved positions in *distinct* residue classes modulo q. Define `U=∑_{t<P} Delta(t)` and `B=∑_{t<P} Delta(t)^2`.

- `moment_certificate_sound`: `(P-1)*B < U^2 → ∀ t : Fin P, 0 < Delta(t)`.
- `moment_certificate_accepted`: Boolean checker soundness for the same finite criterion.
- `certificate_excludes_cover`: the above implies `¬ FullyCovered (P*q) y` **only under the explicit `CRTDispersionBridge P q y` premise**.
- `external_part_ii`: proof-import of `Y(x)=o(x²)` for the actual formal Erdős #687 problem.
- `external_quantitative`: proof-import of `Y(x)=O(x²/(log x log log x)²)`.
- `external_two_blocks`: additional positive two-survivor consequence of OpenAI's iterated-log Jacobsthal theorem.
- `external_plus_certificate`: conjunction of the published external result and the conditional finite BKQR conclusion.

**Missing:** CRT bridge Lean proof; universal near-linear finite witnesses. No assertion of unconditional `Y(x) ≪ x^{1+o(1)}`.

## Pinned, cached CI

`.github/workflows/erdos-687-attempt-f.yml` builds the finite core first, then imports pinned OpenAI/math source and the externally checked formal #687 bridge, and runs per-theorem `#print axioms` with `lean --trust=0`. Build outputs and audit logs are retained as Actions artifacts.

- OpenAI/math source: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- Refereed bridge repository: `634b667ee7844f12590117c4c2d7bc0143f2fdd9`.
- Bridge blob SHA: `64a1cf3ff88a4f655ae7284aa3fb99ed9eab4932`.
- Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Compiler: Lean **4.34.1**, as pinned by the external source; **do not** mix with Lean 4.34.0-rc1 oleans.

No earlier Attempt directories are modified.
