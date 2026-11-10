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
\texttt{NSE\_POINTWISE\_PAIRING\_IDENTIFICATION}^{!!,!!!}
\to
\texttt{NSE\_PAIRING\_POINTWISE\_LP\_LIFT}^{!!,!!!}
\to
\texttt{NSE\_PHYSICAL\_LP\_DATA\_CONSTRUCTION}^{!!,!!!}
\to
\texttt{PERIODIC\_STRONG\_SLICE\_TO\_RAW\_PHYSICAL\_FIELDS}^{!!,!!!}.
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
| `NSE_POINTWISE_PAIRING_IDENTIFICATION.lean` | A_TIER |
| `NSE_PAIRING_POINTWISE_LP_LIFT.lean` | A_TIER |
| `NSE_PHYSICAL_LP_DATA_CONSTRUCTION.lean` | A_TIER |
| `PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS.lean` | A_TIER; derives pairing measurability and constructs `RawPhysicalFields` |
| `H12_CRITICAL_PAIRING_INTEGRAL.lean` | A_TIER_CANDIDATE; current FIX3 source; external native pass pending |

## Latest certified endpoint

`PeriodicStrongSliceToRawPhysicalFields.PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS`

Native Lean 4.33.0 evidence:

```text
COMPILE=PASS
SIGNATURE_CHECK=PASS
THEOREM_AXIOM_AUDITS=8
THEOREM_AXIOM_AUDIT=STANDARD_ONLY
RUN=PASS
ROOT_AXIOMS=propext,Classical.choice,Quot.sound
PAIRING_MEASURABILITY=DERIVED
RAW_PHYSICAL_FIELDS=CONSTRUCTED
```

A periodic strong slice contains

\[
J,u,w\in L^3(\mathbb T^3).
\]

The certified theorem derives almost-everywhere strong measurability of

\[
x\mapsto J(x)u(x)
\]

and

\[
x\mapsto\langle J(x)u(x),w(x)\rangle,
\]

then constructs `RawPhysicalFields` canonically.

Therefore the nonlinear semantic chain is now A-tier complete:

\[
\texttt{PeriodicStrongSlice}
\Longrightarrow
\texttt{RawPhysicalFields}
\Longrightarrow
\texttt{PhysicalLpData}
\Longrightarrow
\texttt{NSEPairingRealization}
\Longrightarrow
\texttt{CriticalHolder}.
\]

With the remaining analytic endpoint `PeriodicHhalfL3`, the certified compiler yields

\[
I_{\rm abs}\le C_3^3ED^2.
\]

Inside the critical radius,

\[
E\le\frac{\nu}{4C_3^3}
\Longrightarrow
I_{\rm abs}\le\frac{\nu}{4}D^2.
\]

## Remaining principal targets

1. formalize `PeriodicHhalfL3`;
2. formalize the rough \(H^{1/2}\) local-existence / continuation interface `H12_LOCAL_CONTINUATION`;
3. compile `H12_SIGMA_SMALL_GLOBAL_REGULARITY`.

Thus the remaining independent seams are exactly

```text
PeriodicHhalfL3
H12_LOCAL_CONTINUATION
```

for the final small-\(H^{1/2}_\sigma\) global regularity theorem.

## Source-layout note

These files preserve their original package imports, for example

```lean
import H12_FOURIER_FOUNDATIONS
```

Therefore this directory should be added to `LEAN_PATH`, or the files should be copied into the project source root, when reproducing the native package builds. The source texts are intentionally not namespace-path rewritten because doing so would alter audited source hashes.

## Native toolchain

Primary certified runs in this assembly used Lean 4.33.0 on native Windows with cached Mathlib and prior A-tier package artifacts.

No claim of unconditional three-dimensional Navier–Stokes global regularity is made by this directory.
