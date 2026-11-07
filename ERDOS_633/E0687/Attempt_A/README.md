# Erdős #687 / Attempt_A — external proof adoption

**Exact endpoint:** `Erdos687.erdos_687.parts.ii`,
`(fun x : ℕ => (Erdos687.Y x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ)^2)`.

**Stronger quantitative endpoint:** `Erdos687.Y_isBigO`,
`Y(x) = O(x² / (log x * log log x)²)`.

## Dependency pins (not unproved local axioms)

- [OpenAI math source](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/Jacobsthal):
  `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- [Refereed Bridge687.lean](https://github.com/pw/erdosproblemaday-verification/blob/634b667ee7844f12590117c4c2d7bc0143f2fdd9/970/openai-jacobsthal-quadratic-refereed/bridge687/Bridge687.lean):
  `634b667ee7844f12590117c4c2d7bc0143f2fdd9`; blob `64a1cf3ff88a4f655ae7284aa3fb99ed9eab4932`.
- Lean `v4.34.1`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

This folder does **not** replace the historical `ERDOS_633/E0687/README.md` snapshot. The external source is fetched by commit rather than copied into this repository.

## Run

CI workflow: [erdos-687-attempt-a.yml](../../../../.github/workflows/erdos-687-attempt-a.yml).

Runs the pinned OpenAI Jacobsthal import DAG with `lake build OAI.NumberTheory.Jacobsthal.Main` and cached Mathlib objects, compiles the original `Bridge687.lean`, compiles `Erdos687AttemptA.lean`, then audits all four precise endpoints with `lean --trust=0` and `#print axioms`. Evidence logs are uploaded even on failure.

Optional Windows `run.cmd` requires externally prepared folders `OAI_LEAN_ROOT` (source `lean` directory of the pinned OpenAI checkout) and `BRIDGE687_SOURCE` (pinned `Bridge687.lean` file), with the exact Lean 4.34.1 toolchain.

**Promotion:** External evidence exists for the source endpoint. This exact Methlib target becomes A_TIER only after its matching CI compilation and theorem-level axiom audit passes. No automatic promotion from preparation.
