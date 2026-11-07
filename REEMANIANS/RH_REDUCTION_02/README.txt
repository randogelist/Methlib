RH_FINITE_DODGSON_PRUNER_433_v0_1_0_CANDIDATE
STATUS=A_TIER_CANDIDATE
TOOLCHAIN=Lean 4.33.0

RUN: call run.cmd
DEPENDENCIES: existing cached native Windows Lean/Mathlib.
NETWORK=NOT_USED
LOCAL_ASSISTANT_LEAN_EXECUTION=NONE

DEFINITION:
  checkPruned(W) = necessaryDodgsonTests(W) && originalCheck(W).

Root soundness is inherited from the original finite checker.
Accepted-witness preservation requires CertifiedDodgsonProjection.
A nontrivial actual-xi determinant projection is not instantiated.
The finite tests and geometric-family rejection concern rational cells;
their semantic connection to a candidate family must be proved.

See RH_FINITE_DODGSON_PRUNER_A_TIER.txt for exact scope and pending obligations.
No RH witness is exhibited.
