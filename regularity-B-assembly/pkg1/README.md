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
\texttt{NSE\_PAIRING\_POINTWISE\_LP\_LIFT}^{!!,!!!}.
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
| `NSE_POINTWISE_PAIRING_IDENTIFICATION.lean` | A_TIER; pointwise pairing unconditional; root conditional on explicit physical realization |
| `NSE_PAIRING_POINTWISE_LP_LIFT.lean` | A_TIER; derives the norm-level `pointwiseLift` field from a.e. physical identifications |
| `H12_CRITICAL_PAIRING_INTEGRAL.lean` | A_TIER_CANDIDATE; current FIX3 source; external native pass pending |

## Latest certified endpoint

`NSEPairingPointwiseLpLift.NSE_PAIRING_POINTWISE_LP_LIFT`

Native Lean 4.33.0 evidence:

```text
COMPILE=PASS
SIGNATURE_CHECK=PASS
THEOREM_AXIOM_AUDITS=8
THEOREM_AXIOM_AUDIT=STANDARD_ONLY
RUN=PASS
ROOT_AXIOMS=propext,Classical.choice,Quot.sound
POINTWISE_LIFT=DERIVED
```

The package proves the generic norm lift

\[
\|q(x)\|
\le
\|f(x)\|\,\|g(x)\|\,\|h(x)\|
\quad\text{a.e.}
\Longrightarrow
\|q\|_{L^1}
\le
\|\texttt{tripleProduct}(f,g,h)\|.
\]

For `PhysicalLpData`, the a.e. identities are

\[
\begin{aligned}
f(x)&=\|u(x)\|,\\
g(x)&=\|J(x)\|,\\
h(x)&=\|w(x)\|,\\
q(x)&=\langle J(x)u(x),w(x)\rangle.
\end{aligned}
\]

The already certified pointwise theorem gives

\[
|\langle J(x)u(x),w(x)\rangle|
\le
\|u(x)\|\,\|J(x)\|\,\|w(x)\|,
\]

so Lean constructs

\[
\texttt{PhysicalLpData}
\Longrightarrow
\texttt{NSEPairingRealization}
\Longrightarrow
\texttt{CriticalHolder}.
\]

With the remaining periodic Sobolev endpoint:

\[
\texttt{PeriodicHhalfL3}
\Longrightarrow
I_{\rm abs}\le C_3^3 E D^2.
\]

Within the critical radius:

\[
E\le \frac{\nu}{4C_3^3}
\Longrightarrow
I_{\rm abs}\le \frac{\nu}{4}D^2.
\]

## Remaining principal targets

1. construct `PhysicalLpData` from the actual periodic velocity, Jacobian, and \(\Lambda u\) fields;
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
