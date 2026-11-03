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
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` (the `v4.34.0-rc1` release).
It downloads Mathlib's cache, verifies all 174 original Lean source hashes and
the original build-plan script, and uses the Linux runner to build and audit
the same 85-stage plan. It rebuilds the package's own objects on Linux.
This Mathlib revision was selected for CI; it is not an identified match for
the earlier external cache. A separate [manual Windows workflow](https://github.com/randogelist/Methlib/actions/workflows/hvr-pnt-windows.yml)
and the original Windows runner remain available.

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
