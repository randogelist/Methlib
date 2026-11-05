# Fefferman B · Periodic regularity at zero force

## Unconditional equivalences

```lean
PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B :
  PeriodicZeroForceGlobalRegularity ↔ B realAnalysis

masterABSemantic_iff_A_and_B :
  MasterABSemantic ↔ (A realAnalysis ∧ B realAnalysis)
```

Both declarations take no construction premise. The forward direction for B is `periodicZeroForceGlobalRegularity_implies_B`. [Endpoint equivalence](ConcreteABCDUnifiedClosure.lean#L2467) · [Joint equivalence](ConcreteABCDUnifiedClosure.lean#L2982) · [Endpoint entry point](FeffermanB.lean)

**`MASTERABSEMANTIC_CONSTRUCTION = OPEN`** in v0.25.0. Constructing `MasterABSemantic` requires proofs of both `WholeSpaceZeroForceGlobalRegularity` and `PeriodicZeroForceGlobalRegularity`. [Definition](ConcreteABCDUnifiedClosure.lean#L2956)

## Standalone build

Copy this directory as a unit. It includes the full v0.25.0 ABCD source, both local Fefferman imports, the dependency lock, the audit and the Windows runner. The external dependency is Mathlib with its locked dependencies for Lean 4.33.0.

On native Windows with Git, elan and Python 3 installed, run `call run.cmd`. On Linux, from this directory:

```sh
set -eu
lake exe cache get
lake build FeffermanB
lake env lean ci/Audit.lean > audit.log
python3 ci/check_axioms.py audit.log
```

The audit requires the B implication, its equivalence, and the six unified declarations. Each report must contain only approved axioms from `{propext, Classical.choice, Quot.sound}`. [Audit declarations](ci/Audit.lean) · [Windows runner](run.cmd) · [Original package notes](README.txt)
