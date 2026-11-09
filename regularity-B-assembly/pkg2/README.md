# regularity-B-assembly / pkg2

Current CEA / BKQR periodic NSE regularity assembly checkpoint.

## Included spine

Externally audited A_TIER modules:
- `CEA07A_BKQRHalfMomentCore.lean`
- `CEA07B_BKQRFiniteSpectralLift.lean`
- `CEA07C_BKQRCriticalWeight.lean`
- `CEA07D_StokesSpectralDictionary.lean`
- `CEA07E_TorusParseval.lean`
- `CEA07F_TorusStokesQuarter.lean`
- `CEA09_ExcessToCritical.lean`
- `CEA10_CriticalToRegularity.lean`
- `CEA11_ConditionalRegularityRoot.lean` — CONDITIONAL_FORMAL_CLOSURE for the explicit certificate-to-Regular implication.

Current active candidate:
- `CEA07G_BKQRActualHalfProduct.lean` — A_TIER_CANDIDATE FIX2. It is not promoted until a matching external native Lean 4.34.0-rc1 compile and theorem-level axiom audit passes.

## Current M2 spine

```text
actual BKQR half product                         CEA07G  [candidate]
  -> BKQRHalfMomentCore                         CEA07A  [A_TIER]
  -> finite spectral lift                       CEA07B  [A_TIER]
  -> critical weight comparison                 CEA07C  [A_TIER]
  -> Stokes spectral dictionary                 CEA07D  [A_TIER]
  -> actual torus Parseval                       CEA07E  [A_TIER]
  -> torus Stokes quarter dictionary             CEA07F  [A_TIER]
  -> excess-action to critical pair              CEA09   [A_TIER]
  -> critical pair to Serrin/regularity           CEA10   [A_TIER]
  -> conditional all-horizons regularity root     CEA11   [A_TIER implication]
```

The finite Fourier/Stokes side through `CEA07F` is A_TIER. The remaining custom M2 gate is the actual BKQR half-product construction in `CEA07G`, followed by the planned exact telescoping/cocycle module `CEA07H`.

## Root status

`CEA11_ConditionalRegularityRoot.lean` formalizes the exact implication from its explicitly stated certificate fields to `Regular`. This is CONDITIONAL_FORMAL_CLOSURE, not unconditional 3D NSE regularity.

No prepared source is promoted merely by being present in this repository.
