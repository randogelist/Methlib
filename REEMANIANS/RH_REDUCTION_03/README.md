# RH_REDUCTION_03 — Quadratic Lyapunov and Cofinal RH Equivalences

**Status: `!! A_TIER` for the exact compiled theorems, verified via user-supplied native Windows Lean 4.33.0 and theorem-level standard-only axiom audit.**

This folder contains the source of the standalone `RH_QUADRATIC_COFINAL_433_v0_2_0_FIX1` package. It reuses the audited `RH_HilbertLimit.AnalyticClosure` and Mathlib modules from the user's existing cached HXY/Mathlib environment.

## Exact scoped theorems

Let `actualSquareEnergy N = ∑ j ∈ Finset.range (N+1), (actualWeight N j)^2`.

- `RHQuadratic.actual_squareEnergy_le_one_iff_nativeRH`
  — `(∀ n, actualSquareEnergy n ≤ 1) ↔ RiemannHypothesis`.
- `RHQuadratic.actual_quadratic_unit_steps_iff_nativeRH`
  — `(∀ n, actualSquareEnergy (n + 1) ≤ actualSquareEnergy n + 1) ↔ RiemannHypothesis`.
- `RHQuadratic.actual_all_scalar_gates_iff_nativeRH`
  — Exact all-degree quadratic successor gate equivalence.
- `RHQuadratic.cofinal_squareEnergy_iff_nativeRH`
  — `(∃ K : ℕ, ∀ cutoff, ∃ n ≥ cutoff, actualSquareEnergy n ≤ K) ↔ RiemannHypothesis`.
- `RHQuadratic.eventual_large_squareEnergy_of_not_nativeRH`
  — Under `¬RiemannHypothesis`, each fixed quadratic bound eventually fails.
- `RHQuadratic.checkRationalSquareGate_sound`
  — Terminating **single-step rational** arithmetic gate soundness.

## Native audit evidence

Native Windows compiler: Lean `4.33.0`, cached Mathlib and HXY; source run `RH_QUADRATIC_COFINAL_433_v0_2_0_FIX1`.

User-provided terminal output:
`COMPILE_PASS=RH_QUADRATIC_LYAPUNOV`,
`COMPILE_PASS=RH_QUADRATIC_COFINAL`,
`RUN=PASS_CANDIDATE_COMPILED_AND_AUDITED`.

User-provided `run-audit.log` lists only `propext`, `Classical.choice`, and `Quot.sound` for the stated root and supporting theorems.

No local Lean execution was performed when this repository folder was prepared.

## Explicitly open

- No accepted actual-ξ finite witness.
- No constructed **fixed terminating** finite-to-universal checker.
- `∀ M, ∃ n≥M, actualSquareEnergy n≤K` is a **cofinal quantified hypothesis**, not one finite accepted certificate.
- Unconditional `RiemannHypothesis` is **not proved**.
- The theorem-level check did not establish a new proof of RH.

## Reproduction

On native Windows with cached Lean 4.33.0 / Mathlib and HXY oleans:

```cmd
cd /d "C:\path\to\Methlib\REEMANIANS\RH_REDUCTION_03"
call run.cmd
```

The runner uses no network, Lake, PowerShell, or HXY baseline rebuilding. Exact source names are preserved to avoid import changes.

## Contents

`RH_QUADRATIC_LYAPUNOV.lean`, `RH_QUADRATIC_COFINAL.lean`,
`Audit.lean`, `AuditCofinal.lean`, `run.cmd`,
`RH_QUADRATIC_COFINAL_B_TIER.txt`,
`RH_QUADRATIC_COFINAL_A_TIER.txt`,
`README.txt`, and this `README.md`.
