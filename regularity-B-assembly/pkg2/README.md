# regularity-B-assembly / pkg2

Current CEA / BKQR periodic NSE regularity assembly checkpoint.

## Included spine

- `CEA07A_BKQRHalfMomentCore.lean` — externally audited A_TIER.
- `CEA07F_TorusStokesQuarter.lean` — externally audited A_TIER physical finite Fourier/Stokes dictionary.
- `CEA07G_BKQRActualHalfProduct.lean` — current A_TIER_CANDIDATE FIX2; not promoted until matching external native Lean 4.34.0-rc1 compile + theorem-level axiom audit passes.
- `CEA11_ConditionalRegularityRoot.lean` — externally audited A_TIER root for certificate -> Regular; status CONDITIONAL_FORMAL_CLOSURE.

## Current M2 spine

```text
actual BKQR half product
  -> BKQRHalfMomentCore
  -> finite spectral / critical-weight chain
  -> actual torus Parseval / Stokes-quarter dictionary
  -> critical regularity compiler
```

The finite Fourier/Stokes side through CEA07F is A_TIER. The active custom M2 gate is CEA07G, followed by the planned exact telescoping/cocycle module CEA07H.

No prepared source is promoted merely by being present in this repository.
