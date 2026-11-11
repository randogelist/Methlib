# Corrections and verification

## Initial assembly

- Preserved the frozen eleven endpoints; physical contracts remain a separate foundation.
- Defined actual periodic NSE semantics, including smoothness through time zero.
- Used smooth order `∞`, not analytic order `ω`.
- Included integrability guards for zero spatial means.
- Kept the universal PDE conclusion as an unproved target definition.
- No local Lean execution; compiler verification is delegated to repository CI.

## CI iteration 1

Commit: `032303bc5774a40c9ff005f083227e65356f6079`.
Run: https://github.com/randogelist/Methlib/actions/runs/42933115745

- Pinned compiler, Mathlib revision, lockfile, cached objects, and source policy passed.
- `SixChannels.lean` compiled.
- Corrected zero-field function derivatives, explicit exponential continuity, and the scoped extended-real notation after compiler diagnostics.
- No endpoint promotion: the full build and fresh theorem audit had not passed.

## Next iteration

- Added finite physical reconstruction and concrete finite-state Galerkin algebra.
- Expanded exact-type audits to the corresponding auxiliary declarations.
- Persist dependency caches before proof compilation; skip disk cleanup when at least 20 GiB is available.

Verification status: candidate repairs pending CI.
