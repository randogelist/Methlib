# Erdős #687 — Attempt_J

**Goal:** Import the pinned external Jacobsthal proof and the already formalized
CRT covering bridge to establish an exact finite **integer Gram admission
equivalence** and a uniform quadratic Gram witness. The external formal proof
also yields **Erdős #687 part (ii): `Y(x)=o(x²)`** and the quantitative
`O(x²/(log x log log x)²)` bound.

**Scoped endpoint (no axiom admission):**

```
OAI.Erdos970.Erdos970Final.erdos_970_quadratic
  + Erdos687.lt_of_covered
  -> noCover_primes_of_jacobsthal
  -> gram_of_jacobsthal
  -> quadratic_uniform_gram
```

**Exact pinning:** Lean 4.34.1; OpenAI math
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, external referee
`634b667ee7844f12590117c4c2d7bc0143f2fdd9`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Files: `Erdos687AttemptJ.lean`, `Audit.lean`,
`ERDOS_687_GRAM_A_TIER.txt`, `ci/run.sh`, `run.cmd`.
Workflow: `.github/workflows/erdos-687-attempt-j.yml`.

**Status:** A_TIER_CANDIDATE until matching remote build and standard-only
theorem-level audit logs pass. **No claim of the stronger open bound
`Y(x)=x^(1+o(1))`.**
