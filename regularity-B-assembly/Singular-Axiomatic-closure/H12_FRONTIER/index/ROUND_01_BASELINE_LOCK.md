# Round 01 — Baseline Lock

## 1. Frozen theorem

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

Exact base scope:

```text
ν > 0
a : CriticalSobolev 1
CriticalSigmaZero a
criticalNonlinearConstant * ‖a‖ < ν
```

Exact conclusion supplies one common evolution with:

```text
CriticalDatumAX6 ν a
CriticalRegularSolution ν a
CriticalLerayHopf membership
Leray–Hopf uniqueness in the registered physical class
PositiveSmoothNSE for t > 0
global L²_t H^(3/2)_x
global L²_t H^(-1/2)_x time derivative
global L⁴_t L⁶_x
sharp quartic-gradient budget
strong H^(1/2) initial trace
```

## 2. Original certification

```text
STATUS=UNCONDITIONAL_CLOSURE
MARKER=!!!!
SOURCE_COMMIT=09dfe94a1ef150e21d09df3013fbe09002ef139c
WORKFLOW_RUN=43059293572
WORKFLOW_JOB=130657144029
COMPILER=external cached Lean 4.33.0
MATHLIB=db584cd6d46c92f209a44c0f1c829460d327499d
EXACT_TYPE_AUDIT=PASS
THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY
AXIOMS=[propext, Classical.choice, Quot.sound]
ADDITIONAL_ANALYTIC_PREMISES=[]
ADDITIONAL_CERTIFICATE_PREMISES=[]
ADDITIONAL_ADMISSION_PREMISES=[]
```

## 3. Copied immutable anchors

```text
SingularClosure/NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean
NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL_A_TIER.txt
NSE_H12_SIGMA_ZERO_SMALL_REGULARITY_A_TIER.txt
H12_SMALL_STATUS.json
verification/h12-final-run.json
ci/critical_audits/SmallDataClosure.lean
ci/critical_audits/SmallDataClosure.json
```

Key copied blob identities:

```text
NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean
  9178f9bd269064a8b15e803d8aa76bf1d5376527

SmallDataRoot.lean
  2c35cd75c35ad52bca3911de9ed7de2841d2db95

SmallDataClosure.lean
  937fca35cfc11b94ea6f5e018939cbb5af5bd15c
```

## 4. Immutability rule

The frontier implementation shall not rewrite the frozen theorem body or its
verified dependencies merely to change a constant name. New declarations are
placed under

```lean
namespace SingularClosure.H12Frontier
```

or in modules named

```text
SingularClosure.H12Frontier.*
```

The original namespace remains available for direct reuse.

## 5. Evidence boundary

The original external evidence proves the original source snapshot. Copying
those files under `H12_FRONTIER` preserves source content but does not promote
future modified files. Every frontier declaration remains
`A_TIER_CANDIDATE` until a matching external cached compiler run and
statement-level axiom audit exist.

## 6. Baseline invariant

Every frontier commit must retain a regression check of the exact original
root type. Failure of that check blocks all extension promotion.