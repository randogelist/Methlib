# H12_FRONTIER

**Core milestones: 14/14 `!=!`.** Unconditional closure for the concrete proved admissible constant instance.  
**Branch:** `H12_extension` · **Compiler:** Lean 4.33.0 · **Local Lean executions:** 0.  
**Fresh cached execution:** [43317474994](https://github.com/randogelist/Methlib/actions/runs/43317474994).  
**E15 remains open:** no strict comparison with the original compiled Methlib coefficient is claimed.

[Summary TXT](FRONTIER_H12_ASSEMBLY_SUMMARY.txt) · [A-tier report](FRONTIER_H12_A_TIER.txt) · [Execution manifest](verification/frontier/EXECUTION.json) · [Root source](SingularClosure/H12Frontier/Root.lean)

## Executed assembly summary

The following block is identical to `FRONTIER_H12_ASSEMBLY_SUMMARY.txt`.

<!-- FRONTIER_H12_ASSEMBLY_SUMMARY_BEGIN -->
```text
FRONTIER_H12 — EXECUTED ASSEMBLY SUMMARY
=======================================

REPOSITORY = randogelist/Methlib
BRANCH = H12_extension
PACKAGE = regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER
STATUS = UNCONDITIONAL_CLOSURE_CONCRETE_ADMISSIBLE_INSTANCE
CORE_MILESTONES_CLOSED = 14/14
MILESTONE_MARKER = !=!
COMPILED_SOURCE_COMMIT = d8b5e510411c224fd7b284b0a65eb2f9b08b3d83
WORKFLOW_RUN = 43317474994
WORKFLOW_JOB = 131529143429
LEAN = 4.33.0
MATHLIB = db584cd6d46c92f209a44c0f1c829460d327499d
LOCAL_LEAN_EXECUTIONS = 0

1. EXACT THEOREM
---------------
Domain: unit T^3 = R^3/Z^3. Forcing: zero.
Datum: a : CriticalSobolev 1 with CriticalSigmaZero a.
The latter means spectral reality, solenoidality and zero mean.

Native norm:
  n(a)^2 = sum_(k != 0) (2*pi*|k|)*|a_hat(k)|^2.
Coefficient norm:
  p(a)^2 = sum_(k != 0) |k|*|a_hat(k)|^2.
Verified identity:
  n(a) = sqrt(2*pi)*p(a).

Fixed constants:
  K2 = sqrt(2)*CSHalf*CSOne*CSZero/(2*pi),
  CF = K2/(2*sqrt(pi)) > 0.

NATIVE ROOT:
  nu > 0, CriticalSigmaZero a, CF*n(a) < nu
    -> datumwise AX6 and one global physical periodic NSE solution.

PUBLIC ROOT:
  nu > 0, CriticalSigmaZero a, p(a) < sqrt(2)*nu/K2
    -> the same full conclusion.

Declarations:
  SingularClosure.H12Frontier.FRONTIER_H12_NATIVE
  SingularClosure.H12Frontier.FRONTIER_H12

The same solution has strong Hhalf initial trace, the uniform bound
n(u(t)) <= n(a), global L2_t HthreeHalf, global L2_t HminusHalf for its actual derivative,
positive-time smooth velocity and pressure, actual NSE, global L4_t L6_x,
physical Leray-Hopf membership, and uniqueness in the registered physical
Leray-Hopf class. Initial smoothness or analyticity is not assumed.

2. CONSTANT SCOPE — REQUIRED QUALIFICATION
-----------------------------------------
CSHalf, CSOne and CSZero are fixed conservative admissible constants derived
from proved physical finite-Fourier estimates and literal Lebesgue dilation.
The nonlinear certificate is constructed and is not an assumed root premise.
The kernel also proves CF = (2*pi)^3*nativeProduct.

The formal radius comparison nu/K2 < sqrt(2)*nu/K2 uses this same fixed K2.
No numerical optimality, historical-priority claim, or theorem for an arbitrary
independently prescribed numerical literature K2 is asserted.

OPTIONAL E15 REMAINS OPEN:
  CF < SingularClosure.criticalNonlinearConstant.
Thus no strict enlargement of the original compiled Methlib ball is asserted.
No BMO/Beltrami/a_dagger extension is part of this root.

3. CLOSED CORE MILESTONES
------------------------
!=! E01  FRONTIER_H12_NORM_BRIDGE
!=! E02  FRONTIER_H12_CONSTANT_NORMALIZATION
!=! E03  FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND
!=! E04  frontierGalerkinEnergyInvariant
!=! E05  frontierDissipationBudget
!=! E06  frontierSharpQuarticBudget
!=! E07  frontierTimeDerivativeBudget
!=! E08  frontierPositiveTimeEnstrophyAccumulation
!=! E09  frontierPositiveTimeH2Bound
!=! E10  frontierPositiveTimeAllOrders
!=! E11  frontierLimitNegativeHalf
!=! E12  frontierLimitSharpQuartic
!=! E13  FRONTIER_H12_NATIVE
!=! E14  FRONTIER_H12

Each marker uses its exact registered concrete type, an external compiler
PASS, and a theorem-level axiom audit. Only propext, Classical.choice and
Quot.sound occur. No sorryAx or auxiliary unresolved certificate is present.
The certificate-parametric support theorems remain correctly distinguished
from their discharged concrete specializations.

4. QUANTITATIVE CONCLUSION
-------------------------
For delta = nu - CF*n(a) > 0 and D_* = criticalTransportConstant:
  integral_0^infinity ||u||_HthreeHalf^2 <= n(a)^2/(2*delta),
  integral_0^infinity ||partial_t u||_HminusHalf^2
    <= (nu+D_* n(a))^2*n(a)^2/(2*delta),
  integral_0^T ||grad u||_2^4
    <= (n(a)^4-n(u(T))^4)/(4*delta).
All conclusions refer to one common Galerkin-limit solution.

5. EXTERNAL EXECUTION AND INTEGRITY
----------------------------------
Workflow: https://github.com/randogelist/Methlib/actions/runs/43317474994
Source: https://github.com/randogelist/Methlib/tree/d8b5e510411c224fd7b284b0a65eb2f9b08b3d83/regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER

14 core exact-type audits: PASS.
12 additional support audit groups: PASS.
51 audited frontier/support declarations: standard-only.
Original unconditional base root regression: PASS.
305 Lean source hashes: matched.
60 generated file hashes: matched.
11 frozen proof-template hashes: matched.
Artifact SHA256: ee4669d58c0741900ff3042e53628c728904f6862de346ba70699ea40cfb7224

Dependency and compiled-project caches were reused. No local Lean execution.
Proof sources were already materialized at bc23626115fa2aad96b1aac76898be376dfa9200;
the fresh replay request changes no Lean source. Documentation added after the
run does not constitute a different compiled theorem snapshot.

6. NATIVE WINDOWS REPLAY
-----------------------
From the H12_FRONTIER package directory:
  call run-frontier.cmd

Pinned Lean 4.33.0, pinned Mathlib, Python 3 and Git are required. Existing
caches are retained. The runner compiles and audits all concrete milestones
and checks the original base root. The root file is not standalone; the
complete package and its pinned dependency cache supply its imports.

7. DEPENDENCY REGISTER
---------------------
index/ENDPOINTS.md                 registered mathematical milestone scopes
index/BASE_IDENTITIES.md           native Methlib identities
index/MATHLIB_IDENTITIES.md        seventeen pinned Mathlib source families
verification/frontier/EXECUTION.json exact current execution and scope record
FRONTIER_H12_A_TIER.txt             exact root signature and audit report

The earlier indexing-only summary is retained as historical documentation.
The README summary block and this summary TXT have identical contents.
```
<!-- FRONTIER_H12_ASSEMBLY_SUMMARY_END -->

## Historical records

The previous indexing-only summary and copied-base README are preserved verbatim:
[historical summary](index/history/FRONTIER_H12_ASSEMBLY_SUMMARY_33bfc91.txt) ·
[historical README](index/history/README_before_execution.md).
Their 0/14 figures describe the earlier indexing snapshot, not the completed execution above.

The original base source and its theorem remain unchanged. The current external regression of that root is recorded in the execution manifest.
