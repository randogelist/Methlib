# regularity-B-assembly / pkg1

Critical periodic \(H^{1/2}\) Navier–Stokes regularity assembly.

This directory preserves the principal Lean source files from the GOODWORKFLOWFRONTIER small-\(H^{1/2}_\sigma\) chain.

## Certified spine

\[
\texttt{H12\_FOURIER\_FOUNDATIONS}^{!!}
\to
\texttt{H12\_SPECTRAL\_ENERGY\_BRIDGE}^{!!}
\to
\texttt{H12\_CRITICAL\_ABSORPTION}^{!!}
\to
\texttt{H12\_CRITICAL\_TRILINEAR\_COMPILER}^{!!,!!!}
\to
\texttt{H12\_HOLDER\_LP\_ADAPTER}^{!!}
\to
\texttt{NSE\_POINTWISE\_PAIRING\_IDENTIFICATION}^{!!,!!!}.
\]

Here:

- `!!` = native A-tier: matching external Lean compiler and theorem-level axiom audit.
- `!!!` = formal closure of the exact implication under explicitly named unresolved premises.

## Current status

| Module | Status |
|---|---|
| `H12_FOURIER_FOUNDATIONS.lean` | A_TIER |
| `H12_SPECTRAL_ENERGY_BRIDGE.lean` | A_TIER |
| `H12_CRITICAL_ABSORPTION.lean` | A_TIER |
| `H12_CRITICAL_TRILINEAR_COMPILER.lean` | A_TIER; CONDITIONAL_FORMAL_CLOSURE |
| `H12_HOLDER_LP_ADAPTER.lean` | A_TIER |
| `NSE_POINTWISE_PAIRING_IDENTIFICATION.lean` | A_TIER; pointwise pairing unconditional; root conditional on `NSEPairingRealization.pointwiseLift` |
| `H12_CRITICAL_PAIRING_INTEGRAL.lean` | A_TIER_CANDIDATE; current FIX3 source; external native pass pending |

## Latest native endpoint

`NSEPointwisePairingIdentification.NSE_POINTWISE_PAIRING_IDENTIFICATION`

Native Lean 4.33.0 evidence:

```text
COMPILE=PASS
SIGNATURE_CHECK=PASS
THEOREM_AXIOM_AUDITS=9
THEOREM_AXIOM_AUDIT=STANDARD_ONLY
RUN=PASS
ROOT_AXIOMS=propext,Classical.choice,Quot.sound
```

The unconditional pointwise theorem is

\[
|\langle Ju,w\rangle|
\le \|u\|\,\|J\|_{\mathrm{op}}\,\|w\|.
\]

The audited root proves

\[
\texttt{NSEPairingRealization}
\Longrightarrow
\texttt{CriticalHolder}.
\]

The remaining semantic field in this layer is exactly

```text
NSEPairingRealization.pointwiseLift
```

which lifts the concrete almost-everywhere pointwise domination to the corresponding \(L^1\)-norm inequality.

## Remaining principal targets

1. discharge `NSEPairingRealization.pointwiseLift` from concrete periodic fields;
2. `PeriodicHhalfL3`;
3. rough \(H^{1/2}\) local existence / continuation interface;
4. final `H12_SIGMA_SMALL_GLOBAL_REGULARITY` root compiler.

## Source-layout note

These files preserve their original package imports, for example

```lean
import H12_FOURIER_FOUNDATIONS
```

Therefore this directory should be added to `LEAN_PATH`, or the files should be copied into the project source root, when reproducing the native package builds. The source texts are intentionally not namespace-path rewritten because doing so would alter audited source hashes.

## Native toolchain

Primary certified runs in this assembly used Lean 4.33.0 on native Windows with cached Mathlib and prior A-tier package artifacts.

No claim of unconditional three-dimensional Navier–Stokes global regularity is made by this directory.
