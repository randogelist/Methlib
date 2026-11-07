# Erdős #687 — Attempt_D

[Problem #687](https://www.erdosproblems.com/687).

## Status

- Finite two-scale sieve inequality: exact theorem candidate in `ERDOS_687.lean`.
- External Jacobsthal quadratic and iterated-log imports: `ERDOS_687_EXTERNAL.lean`, pinned to [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean).
- **Strong endpoint `StrongNoCover`: conditional on `UniformExactMargin`**, not asserted unconditionally.
- No claim of solving the stronger exponent or Erdős #687 from the finite implication alone.

GitHub CI workflow: `.github/workflows/erdos-687-attempt-d.yml`. Native Windows cached runner: `run.cmd`.

Certification: do not label A_TIER unless the exact CI/native Lean 4.34.1 build and theorem-level standard-only axiom audit pass.
