# H12 Representation Classes

```text
WORKFLOW=YOU_ARE_GOODWORKFLOWFRONTIER
SCOPE=regularity-B-assembly
LEAN_EXECUTION=NONE
PROMOTION_POLICY=EXTERNAL_NATIVE_COMPILER_AND_THEOREM_LEVEL_AXIOM_AUDIT_REQUIRED
```

This directory records the current Lean state of the periodic critical
\(H^{1/2}\) representation program.

## Contents

- [`CURRENT_LEANED_H_CLASSES/`](CURRENT_LEANED_H_CLASSES/) — exact register of the presently Leaned \(H\)-class carrier, its compiled structural fields, the current restriction lattice, and unresolved subtype splits.
- [`CURRENT_LEAN_SCOUT_HANDOUT.md`](CURRENT_LEAN_SCOUT_HANDOUT.md) — current ten-representation Lean scout covering Galerkin, Stokes, Poisson, heat, GP, BKQR, Cayley–Sturmion, resolvent/HVR, physical realization, and GP–Borel representations.

## Primary Methlib anchors

- [`../pkg1/H12_FOURIER_FOUNDATIONS.lean`](../pkg1/H12_FOURIER_FOUNDATIONS.lean)
- [`../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean`](../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean)
- [`../pkg1/STATUS.txt`](../pkg1/STATUS.txt)
- [`../pkg2/README.md`](../pkg2/README.md)
- [`../pkg2/CEA07D_StokesSpectralDictionary.lean`](../pkg2/CEA07D_StokesSpectralDictionary.lean)
- [`../pkg2/CEA07E_TorusParseval.lean`](../pkg2/CEA07E_TorusParseval.lean)
- [`../pkg2/CEA07F_TorusStokesQuarter.lean`](../pkg2/CEA07F_TorusStokesQuarter.lean)

## Status convention

```text
A_TIER          = matching external native compilation and theorem-level axiom audit exist
A_TIER_CANDIDATE= prepared Lean source without matching external evidence
B_TIER          = complete mathematical derivation without Lean-kernel promotion
OPEN            = exact representation endpoint not yet constructed
```

No declaration is promoted solely by inclusion in this directory.