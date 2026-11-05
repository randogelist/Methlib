# Fefferman C · Whole-space forced breakdown

```lean
wholeSpaceForcedBreakdown_implies_C :
  WholeSpaceForcedBreakdown → C realAnalysis
```

The implication is unconditional. Deriving `C realAnalysis` by this implication requires a proof of `WholeSpaceForcedBreakdown`. For each positive viscosity, the construction must supply admissible whole-space data and force for which no global solution exists. [Named theorem](ConcreteABCDUnifiedClosure.lean#L2737)

The converse is included in `WHOLESPACE_FORCED_BREAKDOWN_IFF_C`. [Endpoint entry point](FeffermanC.lean)

## Standalone build

Copy this directory as a unit. It includes the full v0.25.0 ABCD source, both local Fefferman imports, the dependency lock, the audit and the Windows runner. The external dependency is Mathlib with its locked dependencies for Lean 4.33.0.

On native Windows with Git, elan and Python 3 installed, run `call run.cmd`. On Linux, from this directory:

```sh
set -eu
lake exe cache get
lake build FeffermanC
lake env lean ci/Audit.lean > audit.log
python3 ci/check_axioms.py audit.log
```

The audit requires the C implication, its equivalence, and the six unified declarations. Each report must contain only approved axioms from `{propext, Classical.choice, Quot.sound}`. [Audit declarations](ci/Audit.lean) · [Windows runner](run.cmd) · [Original package notes](README.txt)
