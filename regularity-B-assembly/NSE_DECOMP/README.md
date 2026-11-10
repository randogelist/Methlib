# NSE_DECOMP — periodic 2D3C rough-trace Navier–Stokes

**Status (2026-11-10): A_TIER_CANDIDATE; conditional root, not FORMAL_CLOSURE.**

The frozen root targets global unforced periodic 3D Navier–Stokes evolution from arbitrary
2D3C divergence-free initial data in $L^2$, strong $L^2$ initial trace,
$C^\infty$ regularity for all positive times, global energy equality,
2D3C invariance, pressure normalization, and **uniqueness among every 3D
Leray–Hopf solution** (not only 2D3C competitors). The strict $L^2\setminus
H^{1/2}$ rough-trace refinement is also tracked.

## Source and evidence separation

* `NSE_DECOMP.lean` — current **v0_1_9_FIX2 candidate**; does **not** have a matching external compiler PASS record in the supplied evidence.
* `verified/v0_1_8/NSE_DECOMP.lean` — last **externally reported** Windows Lean 4.34.0-rc1 `BUILD=PASS` / `AXIOM_AUDIT=STANDARD_ONLY`, with `ROOT_STATUS=CONDITIONAL`.
* `NSE_DECOMP_A_TIER.txt` — exact scope and version information for v0_1_9_FIX2.
* `NSE_DECOMP_B_TIER.txt`, `NSE_DECOMP_REGULARITY_B_TIER.txt` — mathematical derivations; these are not Lean kernel certificates.
* `run.cmd`, `support/run.ps1`, `README_RUN.txt`, `lean-toolchain`, `lakefile.toml` — Windows cached-runner files. They require **a locally installed compatible Lean 4.34.0-rc1 toolchain and prebuilt matching Mathlib cache**; the script does not download/rebuild dependencies. Run from Windows CMD: `call run.cmd` or `call run.cmd -MathlibProject "C:\path\to\cached\project"`.

## Open analytic endpoints

The root proof takes `AnalyticEndpoints` as an **explicit premise**. Those premises, including global 2D $L^2$ NSE evolution, passive scalar smoothing, 3D PDE reconstruction, arbitrary-3D-Leray–Hopf uniqueness, and correspondence with physical weak/strong NSE semantics, are not discharged here. A theorem-level `#print axioms` result omitting `sorryAx` proves only kernel-validity **conditional on the theorem parameters**, not these analytic premises.

The GitHub tree contains **NSE_DECOMP** sources; separate `NSE_NOH` (x1-invariant, existence-only) experiments are not silently merged into this root.

## Independent dependency status

The source imports `Mathlib`, not any Kθ / Mo271 / ζ(5) theorem. A historical runner cache directory called `KTHETA_MO_RC1_CACHE` is shared compiler infrastructure, not a mathematical dependency. 

## External validation

The last user-supplied audit for v0_1_8 states `BUILD=PASS`, `AXIOM_AUDIT=STANDARD_ONLY`, `ROOT_STATUS=CONDITIONAL`. This repository import **has not** been compiled or theorem-audited in the creating environment; `NO_LOCAL_LEAN` is respected.
