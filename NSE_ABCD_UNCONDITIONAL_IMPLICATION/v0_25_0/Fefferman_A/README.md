# Fefferman A · Whole-space regularity at zero force

```lean
wholeSpaceZeroForceGlobalRegularity_implies_A :
  WholeSpaceZeroForceGlobalRegularity → A realAnalysis
```

The implication is unconditional. Deriving `A realAnalysis` by this implication requires a proof of `WholeSpaceZeroForceGlobalRegularity`. For every positive viscosity and every admissible whole-space initial datum, the construction must supply a global solution with zero force. [Named theorem](ConcreteABCDUnifiedClosure.lean#L2893)

The converse is included in `WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A`. [Endpoint entry point](FeffermanA.lean)

## Standalone build

Copy this directory as a unit. It includes the full v0.25.0 ABCD source, both local Fefferman imports, the dependency lock, the audit and the Windows runner. The external dependency is Mathlib with its locked dependencies for Lean 4.33.0.

On native Windows with Git, elan and Python 3 installed, run `call run.cmd`. On Linux, from this directory:

```sh
set -eu
lake exe cache get
lake build FeffermanA
lake env lean ci/Audit.lean > audit.log
python3 ci/check_axioms.py audit.log
```

The audit requires the A implication, its equivalence, and the six unified declarations. Each report must contain only approved axioms from `{propext, Classical.choice, Quot.sound}`. [Audit declarations](ci/Audit.lean) · [Windows runner](run.cmd) · [Original package notes](README.txt)
