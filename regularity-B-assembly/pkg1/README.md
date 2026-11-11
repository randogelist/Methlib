# regularity-B-assembly / pkg1

Periodic critical \(H^{1/2}\) coefficient class and Navier–Stokes estimate assembly.

| Scope | Status |
|---|---|
| Historical ten-module native-passed stack | `A_TIER`, exact ledger scope |
| Carrier, scaling, coefficient embedding, scalar budget | `A_TIER`, exact audited declarations |
| Pairing/convection/HLS compiler roots | `A_TIER`, exact stated premises retained |
| Actual physical small-data global NSE theorem | Open formal endpoint |

Exact statement ledger: [H12_SIGMA_ZERO_SMALL_A_TIER.txt](H12_SIGMA_ZERO_SMALL_A_TIER.txt).

Current certification: **29 exact declarations**, external Linux Lean 4.33.0, compilation and exact-type checks `PASS`, theorem-level axiom audits `STANDARD_ONLY`. Evidence: [run 42941911087](https://github.com/randogelist/Methlib/actions/runs/42941911087), tested commit [`6929a9f4850940f24d7ea5b7770816e7882c6636`](https://github.com/randogelist/Methlib/commit/6929a9f4850940f24d7ea5b7770816e7882c6636), [exact audit manifest](verification/ci_42941911087/audit.json), [evidence directory](verification/ci_42941911087/).

The manifest defines the promotion scope. Compilation of imported modules does not assign individual theorem-level audit status to every auxiliary declaration.

## Concrete small coefficient class

For \(k\in\mathbb Z^3\), set \(\lambda_k=2\pi|k|\). `RealH12Datum` contains a sequence \(a_k\in\mathbb C^3\) satisfying

\[
a_0=0,\quad k\cdot a_k=0,\quad a_{-k}=\overline{a_k},\quad
Q(a):=\sum_k\lambda_k|a_k|^2<\infty.
\]

For \(\nu,C_3>0\),

\[
\operatorname{Small}(\nu,C_3,a)
\iff Q(a)<\left(\frac{\nu}{8C_3^3}\right)^2,
\qquad N(a)=\sqrt{Q(a)}.
\]

`C3` is a numerical parameter. Existence of a physical Sobolev certificate with this constant remains a separate theorem.

| Module containing audited endpoints | Exact conclusion |
|---|---|
| `H12_SIGMA_ZERO_SMALL_CLASS` | Nonempty class; heat and symmetric finite cutoffs preserve smallness |
| `H12_SMALL_SCALING` | \(Q(ra)=r^2Q(a)\), \(N(ra)=|r|N(a)\); arbitrarily small positive scalings; nonzero small data |
| `H12_L2_COEFFICIENT_EMBEDDING` | \(\lambda_k\ge2\pi\) for \(k\ne0\); \(\sum_k|a_k|^2\le Q(a)/(2\pi)\); \(Q(a)=0\iff a=0\) |
| `H12_CRITICAL_ENERGY_BUDGET` | Scalar critical differential inequality and initial smallness imply an integrated bound and square-enstrophy budget |
| `H12_SMALL_CLASS_BUDGET` | Concrete class membership supplies initial smallness for the uniform scalar budget |

These coefficient conclusions do not yet construct physical Fourier synthesis or identify a physical Sobolev norm.

## Exact scalar budget

Let \(H,D,E\) be continuous on \([0,T]\), with \(H,D\ge0\), \(H'=d\) on \([0,T)\), and

\[
H(0)\le H_0,\quad C\sqrt{H_0}\le\theta\nu,\quad
d+2\nu D\le2C\sqrt H\,D,\quad E^2\le HD,
\]

where \(\nu,C>0\), \(\theta<1\), and \(T,H_0\ge0\). The audited theorems derive

\[
H(t)+2(1-\theta)\nu\int_0^tD(s)\,ds\le H_0,
\qquad
\int_0^TE(t)^2\,dt\le\frac{H_0^2}{2(1-\theta)\nu}.
\]

Persistence follows from a barrier argument. Existence of a budget is a conclusion. `Small ν C3 a` supplies \(C_3^3\sqrt{Q(a)}\le\nu/4\), so the indexed specialization \(H_0=Q(a)\), \(C=C_3^3\), \(\theta=1/4\) gives

\[
\forall n,\qquad\int_0^TE_n(t)^2\,dt\le\frac{2Q(a)^2}{3\nu}.
\]

The bound is independent of the index and terminal time. Continuity, nonnegativity, the derivative and critical differential law, the initial comparison, and interpolation remain explicit hypotheses on each interval.

The intended physical identifications

\[
H_n=\|u_n\|_{\dot H^{1/2}}^2,\quad
D_n=\|u_n\|_{\dot H^{3/2}}^2,\quad
E_n=\|\nabla u_n\|_2^2
\]

remain Galerkin obligations. The scalar declarations construct no NSE trajectory.

## Historical native-passed overlay

The historical native Windows Lean 4.33.0 evidence is retained separately from the current Linux certification.

Use:

```lean
import LEAN_PASSED_STACK
```

as the import surface for passed material only. The exact package versions, source hashes, theorem names, and evidence directories are recorded in:

```text
LEAN_PASSED_STACK.txt
```

The historical import surface contains ten native-passed modules. Its exact source hashes and certification scope remain those of `LEAN_PASSED_STACK.txt`. The new aggregate and current 29-declaration certification have their own source manifest.

## Historical certified spine

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

`!!` denotes `A_TIER`. `!!!` denotes formal closure of the exact implication under explicitly named remaining premises.

## Historical component endpoint

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

## Audited HLS compiler endpoint

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

This exact HLS compiler root is `A_TIER` in the current 29-declaration audit. The bounded physical operator and reconstructions remain explicit premises.

## Remaining physical endpoints

1. **Fourier realization:** physical real, mean-zero, weakly divergence-free data; \(Q(a)=\|u_0\|_{\dot H^{1/2}}^2\); physical \(L^2\) realization and critical cutoff convergence.
2. **Periodic Sobolev endpoint:** construct and bound \(\Lambda^{-1/2}:L^2_0(\mathbb T^3)\to L^3(\mathbb T^3)\), with the required reconstructions. The HLS compiler assumes these certificates.
3. **Physical Galerkin linkage:** actual finite trajectories from critical data; critical differential law; spectral interpolation; pairing identities; initial comparison.
4. **Continuum evolution:** compactness and nonlinear convergence; physical NSE and pressure equations; strong critical initial trace; global dissipation; uniqueness in an explicitly specified class; positive-time smoothing and continuation.

`H12_LOCAL_CONTINUATION` is an unresolved analytic endpoint label. Finite Galerkin existence elsewhere does not itself discharge these obligations.

The physical target is a unique global critical periodic NSE evolution for real, mean-zero, divergence-free data satisfying

\[
\|u_0\|_{\dot H^{1/2}}<\frac{\nu}{8C_3^3},\qquad
u\in C([0,\infty);H^{1/2})\cap L^2((0,\infty);H^{3/2}),
\]

smooth for positive time. Its mathematical derivation is recorded in [H12_SIGMA_SMALL_GLOBAL_REGULARITY_B_TIER.txt](H12_SIGMA_SMALL_GLOBAL_REGULARITY_B_TIER.txt). Certification of the exact carrier/scalar declarations does not promote that physical root to `A_TIER`, `FORMAL_CLOSURE`, or `UNCONDITIONAL_CLOSURE`.

## Source-layout note

The files preserve their original bare imports. Add this directory to `LEAN_PATH`, or copy the files into the project source root, when replaying the native package builds.

## Aggregate and external cached replay

```lean
import H12_SIGMA_ZERO_SMALL_PACKAGE
```

The aggregate includes the current audited roots and their dependencies. The exact 29 declarations are listed in [audit.json](verification/ci_42941911087/audit.json), with raw theorem axioms in [axioms.log](verification/ci_42941911087/axioms.log) and tested source hashes in [sources.sha256](verification/ci_42941911087/sources.sha256).

| Dependency | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Approved theorem axioms | `propext`, `Classical.choice`, `Quot.sound` |

Native Windows replay, using existing cached dependencies:

```bat
call run.cmd
call run.cmd -MathlibCache "C:\path\to\cached\mathlib4"
call run.cmd -MathlibCache "C:\path\to\cached\mathlib4" -LeanExe "C:\path\to\lean.exe"
```

Optional defaults: `H12_MATHLIB_CACHE`, `H12_LEAN_EXE`. `run.cmd` delegates to `support/run.ps1`; on execution, compiler/cache validation, compilation, signature checks, and theorem-level axiom audits are recorded in a unique `evidence/<run-id>/` directory. The runner requires a clean pinned cached Mathlib checkout and a direct native compiler; dependency installation/download is not performed.

The current successful compiler run was external Linux. The Windows runner received a remote PowerShell syntax parse; current Windows end-to-end execution is not claimed. No local Lean execution occurred.

The canonical evidence artifact has SHA256 `591b33f55a24b3b58326fe590de0a778ebf4b097ddad8a5e14bb2d604029a50a`. Promotion is restricted to the exact checked declarations and matching tested sources; `sorryAx` and unapproved axioms are absent.

