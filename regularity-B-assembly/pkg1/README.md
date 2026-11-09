# regularity-B-assembly / pkg1

Critical periodic (H^{1/2}) Navier–Stokes regularity assembly.

This directory preserves the principal Lean source files from the GOODWORKFLOWFRONTIER small-(H^{1/2}_\sigma) chain.

## Certified spine

[
H12\_FOURIER\_FOUNDATIONS^{!!}
\to
H12\_SPECTRAL\_ENERGY\_BRIDGE^{!!}
\to
H12\_CRITICAL\_ABSORPTION^{!!}
\to
H12\_CRITICAL\_TRILINEAR\_COMPILER^{!!,!!!}
\to
H12\_HOLDER\_LP\_ADAPTER^{!!}.
]

Here:

- `!!` = native A-tier: matching external Lean compiler + theorem-level axiom audit.
- `!!!` = formal closure of the exact implication under explicitly named unresolved premises.

## Current status

| Module | Status |
|---|---|
| `H12_FOURIER_FOUNDATIONS.lean` | A_TIER |
| `H12_SPECTRAL_ENERGY_BRIDGE.lean` | A_TIER |
| `H12_CRITICAL_ABSORPTION.lean` | A_TIER |
| `H12_CRITICAL_TRILINEAR_COMPILER.lean` | A_TIER; CONDITIONAL_FORMAL_CLOSURE |
| `H12_HOLDER_LP_ADAPTER.lean` | A_TIER |
| `H12_CRITICAL_PAIRING_INTEGRAL.lean` | A_TIER_CANDIDATE; current FIX3 source, external native pass pending |

## Remaining principal targets

1. `NSE_POINTWISE_PAIRING_IDENTIFICATION`
2. `PeriodicHhalfL3`
3. rough (H^{1/2}) local existence / continuation interface
4. final `H12_SIGMA_SMALL_GLOBAL_REGULARITY`

## Important source-layout note

These files are preserved as the exact package sources with their original bare imports, e.g.

`import H12_FOURIER_FOUNDATIONS`.

Therefore the directory itself should be added to `LEAN_PATH`, or the files should be copied into the project source root, when reproducing the original native package builds. The source texts are intentionally not namespace-path rewritten, because doing so would alter the audited source hashes.

## Native toolchain

Primary certified runs in this assembly used Lean 4.33.0 on native Windows, with cached Mathlib / prior A-tier package artifacts.

No claim of unconditional 3D Navier–Stokes global regularity is made by this directory.
