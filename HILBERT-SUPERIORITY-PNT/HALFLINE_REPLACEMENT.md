# Half-line dominated-convergence replacement

The branch preserves the theta PNT statement and its 85-stage build plan. `HVR_HalfLine_IndicatorConvolution.lean` preserves the original namespace, convolution definition, and all three theorem signatures. Its cumulative-integral proof now splits the real integral into positive and negative parts and uses monotone lower-integral exhaustion. It replaces one direct use of `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.

Cached Linux Lean 4.34.0-rc1 [CI run 41732097102](https://github.com/randogelist/Methlib/actions/runs/41732097102) built and named-axiom-audited the full theta PNT root with the replacement. The checked half-line source SHA-256 is `0a9e605643a834bc1fd15a92a81a0bc1ccb6bb135bbdf31fee78bd317bde4b4b`.

A controlled proof-term diagnostic detected all four direct/two-hop positive controls. Neither selected sequential nor filter DCT declaration was seen in `HVRHalfLineIndicatorConvolution.integral_Iic_tendsto_integral` or `.halfLineConvolution_tendsto_one`; it reported zero unavailable reached theorem bodies, zero missing declarations, and zero declarations from the target DCT module. Negative dependency coverage remains **UNVERIFIED**, and no semantic independence from equivalent results is claimed.

The same diagnostic **found both selected declarations in the PNT root**, including 17 reached declarations from the DCT module. This is one integrated local replacement, not removal of dominated convergence from the full PNT chain. Other source applications and zeta/boundary infrastructure remain.

The PNT job verifies `branch_sources.sha256`; its only changed content entry relative to the retained historical `original_sources.sha256` is `HVR_HalfLine_IndicatorConvolution.lean`. Lean 4.34.0-rc1, the pinned Mathlib revision, cached Mathlib, and the 85-stage plan are unchanged. [Root CI evidence](https://github.com/randogelist/Methlib/actions/runs/41732097102/artifacts/13278066461) records the checked build and diagnostic.
