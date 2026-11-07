# RH_REDUCTION_01

A-tier RH reduction project with a proof-carrying single-mode witness and certified finite margin cross-outs.

## Verified roots

Native Windows Lean 4.33.0 passed with theorem-level standard-only axiom audit for:

- `RHShiftedHausdorff.NSEJoint.SingleModeWitness.nativeRH`
- `RHShiftedHausdorff.NSEJoint.SingleModeKernel.verify_sound`
- `RHShiftedHausdorff.NSEJoint.MarginExclusion.no_singleModeWitness`
- `RHShiftedHausdorff.NSEJoint.MarginCrossoutDatabase.filteredCheck_eq_baseCheck`
- `RHShiftedHausdorff.NSEJoint.MarginCrossoutDatabase.filteredVerify_sound`

## Meaning

A checked single-mode witness implies literal Mathlib `RiemannHypothesis`.

A finite failed Bernstein-margin cell excludes the entire corresponding `K` family.

Certified cross-outs preserve the accepted witness set exactly.

Concrete accepted-witness existence remains open.

## Source layout

The current reduction spine is retained directly under `RHShiftedHausdorff/NSEJoint/`. The earlier Hilbert/HXY backend is imported from the existing REEMANIANS material.
