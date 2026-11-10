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
\texttt{NSE\_PHYSICAL\_LP\_DATA\_CONSTRUCTION}^{!!,!!!}.
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
| `NSE_PHYSICAL_LP_DATA_CONSTRUCTION.lean` | A_TIER; constructs all physical `Lp` representatives and proves the actual pairing is in `L¹` |
| `PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS.lean` | A_TIER_CANDIDATE |

## Latest certified endpoint

`NSEPhysicalLpDataConstruction.NSE_PHYSICAL_LP_DATA_CONSTRUCTION`

Native Lean 4.33.0 evidence:

```text
COMPILE=PASS
SIGNATURE_CHECK=PASS
THEOREM_AXIOM_AUDITS=12
THEOREM_AXIOM_AUDIT=STANDARD_ONLY
RUN=PASS
ROOT_AXIOMS=propext,Classical.choice,Quot.sound
PHYSICAL_LP_DATA=CONSTRUCTED
PAIRING_MEMLP_ONE=DERIVED
```

The package starts from `RawPhysicalFields`:

\[
J,u,w\in L^3,
\qquad
x\mapsto \langle J(x)u(x),w(x)\rangle
\text{ measurable}.
\]

It derives

\[
|u|\,|J|\,|w|\in L^1,
\qquad
\langle Ju,w\rangle\in L^1,
\]

constructs canonical `MemLp.toLp` representatives, and proves

\[
\texttt{RawPhysicalFields}
\Longrightarrow
\texttt{PhysicalLpData}
\Longrightarrow
\texttt{CriticalHolder}.
\]

With `PeriodicHhalfL3`:

\[
I_{\rm abs}\le C_3^3ED^2.
\]

Inside the critical radius:

\[
E\le\frac{\nu}{4C_3^3}
\Longrightarrow
I_{\rm abs}\le\frac{\nu}{4}D^2.
\]

## Current candidate endpoint

`PeriodicStrongSliceToRawPhysicalFields.PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS`

A periodic strong slice supplies

\[
J,u,w\in L^3(\mathbb T^3).
\]

The candidate derives measurability of

\[
x\mapsto\langle J(x)u(x),w(x)\rangle
\]

from continuity of continuous-linear-map application and the real inner product, then constructs `RawPhysicalFields` canonically.

After promotion, the nonlinear semantic chain is complete up to the sole independent analytic endpoint

```text
PeriodicHhalfL3
```

and the later global theorem additionally requires

```text
H12_LOCAL_CONTINUATION
```

## Remaining principal targets

1. promote `PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS`;
2. formalize `PeriodicHhalfL3`;
3. formalize the rough \(H^{1/2}\) local-existence / continuation interface;
4. compile `H12_SIGMA_SMALL_GLOBAL_REGULARITY`.

## Source-layout note

These files preserve their original package imports, for example

```lean
import H12_FOURIER_FOUNDATIONS
```

Therefore this directory should be added to `LEAN_PATH`, or the files should be copied into the project source root, when reproducing the native package builds. The source texts are intentionally not namespace-path rewritten because doing so would alter audited source hashes.

## Native toolchain

Primary certified runs in this assembly used Lean 4.33.0 on native Windows with cached Mathlib and prior A-tier package artifacts.

No claim of unconditional three-dimensional Navier–Stokes global regularity is made by this directory.
