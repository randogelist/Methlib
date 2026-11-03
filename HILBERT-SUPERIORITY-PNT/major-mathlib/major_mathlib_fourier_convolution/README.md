# HVR candidate: Real.fourier_mul_convolution_eq

Candidate theorem: `NativeFourierConvolution.real_complex_convolution_product`. See its `_A_TIER.txt` file for exact scope, premises, and remaining work. This branch is separate from the PNT root.

Windows: set `MATHLIB_CACHE_ROOT` to a compatible cached Mathlib checkout and call `run.cmd`. The checked-in `plan.json` defines ordered source builds and the named theorem-level axiom audit. `run.cmd -TraceDependencies` requests the optional dependency diagnostic, whose negative coverage is unverified.

Linux CI checks Mathlib revision `fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0`, uses its downloaded cache, Lean 4.34.0-rc1, builds the checked-in sources, and audits the named theorem. A green build does not establish independence from Mathlib.
