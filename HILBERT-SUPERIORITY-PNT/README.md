# Hilbert–Superiority PNT

> The original half-line cumulative-integral proof has been replaced with a monotone lower-integral route. See [HALFLINE_REPLACEMENT.md](HALFLINE_REPLACEMENT.md) for verification scope and provenance. The original PNT source manifest remains historical; the PNT CI verifies `branch_sources.sha256`.

[![HVR theta PNT Linux — main-branch CI](https://github.com/randogelist/Methlib/actions/workflows/hvr-pnt.yml/badge.svg?branch=main)](https://github.com/randogelist/Methlib/actions/workflows/hvr-pnt.yml)

## Unconditional theta theorem

The root theorem states the theta form of the prime number theorem:

```lean
HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one :
  Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)
```

[Root source](HVR_PrimeDensity_FinalRoot.lean) ·
[Named axiom audit](Audit_HVR_PrimeDensity_FinalRoot.lean) ·
[CI runs and evidence](https://github.com/randogelist/Methlib/actions/workflows/hvr-pnt.yml)

The badge shows the latest **main-branch workflow** result; it is not a separate
per-theorem badge. The workflow builds the 85 staged modules and audits their
named declarations, including the root theorem and its two named supporting
declarations. The runner rejects missing audit reports and axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. Open a run above and download
its `hvr-theta-linux-evidence` artifact for its logs and recorded hashes.

An earlier external Windows run of the original source package was reported to have passed the root build and
named standard-axiom audit. Its full Mathlib cache provenance was not recorded.
The GitHub Actions run is a separate reproduction attempt: check its actual
result before claiming that CI has passed. Neither an axiom audit nor a green
badge establishes independence from other PNT proofs.

## Lean source size

Counts are for the `*.lean` files in this folder, excluding Mathlib and other
dependencies. A physical line includes blank lines, comments and imports;
nonblank lines still include comments and imports.

| Files | Lean files | Physical lines | Nonblank lines |
|---|---:|---:|---:|
| Source modules, excluding trace files | 85 | 5,568 | 4,935 |
| Named audit files (`Audit_*.lean`) | 85 | 505 | 485 |
| Diagnostic trace files | 4 | 288 | 268 |
| **Total** | **174** | **6,361** | **5,688** |

The [final root file](HVR_PrimeDensity_FinalRoot.lean) has **52 physical
lines** and its audit file has **7**. The root imports earlier modules, so 52
lines is not the size of the complete proof. The source-module count is a
package-wide count; it is not a minimal dependency or proof-only count.

To reproduce the totals from this directory:

```python
from pathlib import Path

files = list(Path(".").glob("*.lean"))
lines = [line for path in files
         for line in path.read_text(encoding="utf-8").splitlines()]
print("Lean files:", len(files))
print("Physical lines:", len(lines))
print("Nonblank lines:", sum(bool(line.strip()) for line in lines))
```

## Reproduction

GitHub Actions uses Linux Lean `4.34.0-rc1` and Mathlib commit
`fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0` (an RC1-toolchain-compatible revision).
It downloads Mathlib's cache, verifies all 174 branch Lean source hashes and
the original build-plan script, and uses the Linux runner to build and audit
the same 85-stage plan. It rebuilds the package's own objects on Linux.
This Mathlib revision was selected for CI; it is not an identified match for
the earlier external cache. The original Windows runner remains available.

The workflow checks these unchanged root source hashes before building:

* `HVR_PrimeDensity_FinalRoot.lean`: `69c5ed8806b9cec089e70c4dc7422e5f442feef1d4138b51a355e0475d04423b`
* `Audit_HVR_PrimeDensity_FinalRoot.lean`: `84fbc235a599207ccfcd894a5c47646394c579b1827f70b6078a4664b0ff6136`

The runner records compiler, source and object hashes. Hashes establish byte
identity, not independent authentication of a prior run or proof-route
independence.

For a local Windows run with an already populated compatible Mathlib cache:

```cmd
set "MATHLIB_CACHE_ROOT=C:\path\to\mathlib"
call run.cmd
```

The original source package came from `HVR_PNT_THETA_ASSEMBLY_RC1_FIX2.zip`; the project replaces the half-line proof as described above. The original package SHA-256 is
`1691e27682d7be2dd52fa4cae841d5b73a5034a5f11d4767068a49009f0a7566`.

## Additional prime-power and zeta bridge

The [`native-rebuild/`](native-rebuild/) subdirectory contains a separate
Lean development of the prime-power reindexing and zeta logarithmic-derivative
bridge. Its named root is
`HVRNextEulerPrimeZetaBridge.eulerProductLogDerivative`, of type
`HVRNativeZetaLogDerivative.EulerProductLogDerivative`. For `s : ℂ` with
`1 < s.re`, that proposition states

```math
  \sum_p \frac{\log(p)\,p^{-s}}{1-p^{-s}}
  = -\frac{\zeta'(s)}{\zeta(s)}.
```

The Lean statement uses a totalized `tsum`; it is not a separate theorem
asserting summability of the outer prime series. The result is a bridge in the
right half-plane, not a proof of the PNT root above. The replacement bridge
has **not** been wired into the original PNT proof: in particular, the
original [`HVR_Zeta_LogDerivative.lean`](HVR_Zeta_LogDerivative.lean) directly
uses Mathlib's `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

In [Linux CI run 41712052899](https://github.com/randogelist/Methlib/actions/runs/41712052899),
all 26 modules compiled and all 41 named declarations passed the standard-only
axiom audit, including the exact bridge root. The **overall run failed** its
separate full dependency gate: the root trace found the following 14 named
Mathlib declarations indirectly used:

```text
ArithmeticFunction.coe_mul_zeta_apply
ArithmeticFunction.coe_zeta_mul_apply
ArithmeticFunction.coe_zeta_smul_apply
Complex.cpow_def_of_ne_zero
Complex.cpow_nat_mul
Complex.natCast_log
Complex.norm_exp
Complex.ofReal_log
HasSum.mul_left
HasSum.tsum_eq
LSeries.norm_term_eq
Nat.sum_divisors_prime_pow
Summable.of_nonneg_of_le
Summable.of_norm
```

Other inspected names were not seen by that trace, whose coverage is
explicitly unverified; this is not a certificate of their complete transitive
absence. The proofs retain Mathlib's definitions and general arithmetic,
factorization, complex analysis and L-series infrastructure. Some source
comments describe the pre-CI candidate state; the hash-matched source was
subsequently compiled and audited in the linked run. The Mathlib proofs adapted
in the package retain their attribution and Apache 2.0 license.

The [HVR zeta bridge Linux workflow](https://github.com/randogelist/Methlib/actions/workflows/hvr-native-bridge.yml)
rebuilds the named declarations and retains the full dependency trace. Its
`--allow-known-dependencies` mode records the previously observed findings
against hash-pinned source and theorem names; new findings or mismatched source
do not qualify for that allowance. Its success means the build and named axiom
audits passed, not that the bridge is independent of the listed dependencies.
Check the actual workflow result and its uploaded evidence for each run.

To run the named-theorem build and axiom audits on Windows using a populated
compatible cache, from this directory:

```cmd
set "MATHLIB_CACHE_ROOT=C:\path\to\mathlib"
call "native-rebuild\run.cmd"
```

The optional command `call "native-rebuild\run.cmd" -TraceDependencies` also
checks the full target list and is expected to report a failing dependency gate
while the known targets above remain present. A normal runner pass does not
certify dependency coverage. Compiler and full Mathlib cache provenance remain
distinct: the latter is not independently established by the source hashes.

The earlier 22-candidate source set is retained separately in
[`native22-rebuild/`](native22-rebuild/), and the original spectral amendment
and native-chain package are retained in
[`prime-spectral-amendment/`](prime-spectral-amendment/) and
[`native-lean-chain/`](native-lean-chain/). They are separate packages with
their own proof scopes and audits; inclusion here does not merge their
theorems into the original PNT root.


The original downloadable derivation packages and their historical evidence are also retained under [`archives/`](archives/).

## Major Mathlib replacement candidates

The [`major-mathlib/`](major-mathlib/) directory contains the ten separately developed candidates below. Each subdirectory contains its checked-in source plan, source hashes, scope notes, and a `run.cmd` for a compatible Windows Mathlib cache. The Linux candidate workflow rebuilds and audits the named declarations using cached Lean 4.34.0-rc1 and the pinned Mathlib revision. A passing named-theorem audit covers the theorem as stated, including any hypotheses; it does not certify transitive independence from Mathlib.

| Candidate | Current scope |
|---|---|
| [`major_mathlib_von_mangoldt_log_derivative`](major-mathlib/major_mathlib_von_mangoldt_log_derivative/) | Actual von Mangoldt L-series and zeta log derivative on `1 < s.re`. A separate audited candidate; it is not substituted into the PNT root. |
| [`major_mathlib_zeta_nonzero`](major-mathlib/major_mathlib_zeta_nonzero/) | Actual zeta nonvanishing on `1 < s.re`, using a Möbius inverse and Mathlib L-series infrastructure. |
| [`major_mathlib_zeta_analytic`](major-mathlib/major_mathlib_zeta_analytic/) | Actual zeta analyticity away from 1, using Mathlib's regularized-zeta infrastructure; foundational independence is not established. |
| [`major_mathlib_zeta_pole_asymptotic`](major-mathlib/major_mathlib_zeta_pole_asymptotic/) | Regularized zeta log-derivative little-o statement at the pole, including Euler's constant. |
| [`major_mathlib_chebyshev_bound`](major-mathlib/major_mathlib_chebyshev_bound/) | The bound `Chebyshev.theta x ≤ Real.log 4 * x` for `0 ≤ x`. |
| [`major_mathlib_lseries_integral`](major-mathlib/major_mathlib_lseries_integral/) | Conditional prime-weight Mellin limit transfer from finite Abel summation. The required convergence hypotheses and the full general L-series/integral theorem are not proved by this candidate. |
| [`major_mathlib_fourier_decay`](major-mathlib/major_mathlib_fourier_decay/) | Compact-support Fourier decay in both frequency directions and the actual patched-boundary application. The HVR route adapts an attributed Mathlib proof; it has not been substituted into the original PNT Fourier modules. |
| [`major_mathlib_fourier_convolution`](major-mathlib/major_mathlib_fourier_convolution/) | Convolution-product identity for integrable complex functions on the real line, using a Mathlib bilinear convolution integral formula. |
| [`major_mathlib_fubini_swap`](major-mathlib/major_mathlib_fubini_swap/) | Separable-integrand and fixed-frequency identities only; the coupled PNT interchange and general Fubini remain separate. |
| [`major_mathlib_dominated_convergence`](major-mathlib/major_mathlib_dominated_convergence/) | An abstract compact-uniform integral transfer and the actual PNT compact-frequency boundary limit. The actual boundary proof still reaches the selected dominated-convergence declarations through upstream analytic infrastructure. The separate half-line kernel proof has been substituted into the PNT module; see [HALFLINE_REPLACEMENT.md](HALFLINE_REPLACEMENT.md). |

The half-line replacement preserves the PNT theorem and its 85-stage build plan. In [cached Linux CI run 41732097102](https://github.com/randogelist/Methlib/actions/runs/41732097102), the modified half-line source and full PNT root built and passed named standard-only axiom audits. A controlled diagnostic found neither selected dominated-convergence declaration in the two modified half-line theorems, but **found both in the full PNT root**. Negative trace coverage remains unverified; this does not establish semantic or general Mathlib independence.

The Fourier compact-support candidate passed its own [cached Linux CI run 41726247514](https://github.com/randogelist/Methlib/actions/runs/41726247514). Its controlled trace did not see the selected Fourier endpoint in the scoped candidate roots, with negative coverage unverified. This does not mean the candidate has replaced the original Fourier call in the PNT chain.
