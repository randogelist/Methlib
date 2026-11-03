# Hilbert–Superiority PNT

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

An earlier external Windows run was reported to have passed the root build and
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
| Source modules, excluding trace files | 85 | 5,539 | 4,906 |
| Named audit files (`Audit_*.lean`) | 85 | 505 | 485 |
| Diagnostic trace files | 4 | 288 | 268 |
| **Total** | **174** | **6,332** | **5,659** |

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
It downloads Mathlib's cache, verifies all 174 original Lean source hashes and
the original build-plan script, and uses the Linux runner to build and audit
the same 85-stage plan. It rebuilds the package's own objects on Linux.
This Mathlib revision was selected for CI; it is not an identified match for
the earlier external cache. The original Windows runner remains available.

The workflow checks these original source hashes before building:

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

The unchanged source package came from `HVR_PNT_THETA_ASSEMBLY_RC1_FIX2.zip`,
SHA-256 `1691e27682d7be2dd52fa4cae841d5b73a5034a5f11d4767068a49009f0a7566`.

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
