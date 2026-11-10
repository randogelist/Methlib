# regularity-B-assembly / pkg1

Critical periodic \(H^{1/2}\) Navier–Stokes regularity assembly.

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
\texttt{PERIODIC\_STRONG\_SLICE\_TO\_RAW\_PHYSICAL\_FIELDS}^{!!,!!!}
\to
\texttt{PERIODIC\_HHALF\_L3\_COMPONENT\_COMPILER}^{!!,!!!}.
\]

`!!` denotes native Lean A-tier. `!!!` denotes formal closure of the exact implication under explicitly named remaining premises.

## Latest certified endpoint

`PeriodicHhalfL3ComponentCompiler.PERIODIC_HHALF_L3_COMPONENT_COMPILER`

```text
COMPILE=PASS
SIGNATURE_CHECK=PASS
THEOREM_AXIOM_AUDITS=10
THEOREM_AXIOM_AUDIT=STANDARD_ONLY
RUN=PASS
ROOT_AXIOMS=propext,Classical.choice,Quot.sound
COMMON_CONSTANT=C3_EQ_9_MUL_CSCALAR
VECTOR_MATRIX_LIFT=DERIVED
```

The data compiler

```lean
PeriodicHhalfL3ComponentCompiler.toPeriodicHhalfL3
```

maps a componentwise scalar endpoint certificate to the exact `PeriodicHhalfL3` structure. The theorem-level root proves existence of a witness with

\[
C_3=9C_{\rm scalar}.
\]

Hence the vector/matrix part of the periodic critical Sobolev endpoint is certified:

\[
\|u\|_{L^3}\le C_3E,
\qquad
\|\nabla u\|_{L^3,\mathrm{op}}\le C_3D,
\qquad
\|\Lambda u\|_{L^3}\le C_3D.
\]

## Current candidate endpoint

`ScalarPeriodicHhalfL3HLSCompiler.SCALAR_PERIODIC_HHALF_L3_HLS_COMPILER`

It reduces the scalar endpoint to a bounded periodic Riesz-half operator

\[
\Lambda^{-1/2}:L^2_0(\mathbb T^3)\to L^3(\mathbb T^3),
\qquad
\|\Lambda^{-1/2}g\|_3\le C_{\rm HLS}\|g\|_2.
\]

Given the operator certificate and component reconstructions, the package constructs `PeriodicHhalfL3` with

\[
C_3=9C_{\rm HLS},
\]

then reuses the certified nonlinear chain to obtain

\[
I_{\rm abs}\le C_3^3ED^2,
\]

and, inside the critical radius,

\[
I_{\rm abs}\le\frac{\nu}{4}D^2.
\]

## Remaining exact seams

```text
PERIODIC_RIESZ_HALF_L2_L3
H12_LOCAL_CONTINUATION
```

These imply the final target

```text
H12_SIGMA_SMALL_GLOBAL_REGULARITY
```

with threshold \(\nu/(8C_3^3)\).

## Source-layout note

The files preserve their original bare imports. Add this directory to `LEAN_PATH`, or copy the files into the project source root, when replaying the native package builds.

## Native toolchain

Primary certified runs use native Windows Lean 4.33.0 and cached Mathlib/prior A-tier artifacts.

No unconditional three-dimensional Navier–Stokes global-regularity claim is made by this directory.
