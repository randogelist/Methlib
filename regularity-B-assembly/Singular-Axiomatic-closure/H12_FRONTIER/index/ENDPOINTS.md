# FRONTIER_H12: endpoint organization v2

```text
REPOSITORY=randogelist/Methlib
BRANCH=H12_extension
PACKAGE=regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER
NAMESPACE=SingularClosure.H12Frontier
CORE_MILESTONES=14
REPLAY_MILESTONES=9
OPTIONAL_COMPARISON=E15
STATUS=PLANNED_NOT_COMPILED
```

## 0. Scope and counting convention

The target retains the centered smallness form for unforced periodic NSE:

    nu > 0, a in H^(1/2)_{sigma,0}, C_F * norm_native(a) < nu
      -> one global physical solution with the full quantitative conclusion.

The carrier, equation, viscosity, mean-zero/solenoidal conditions, strong
initial trace, positive-time smoothness, and uniqueness class are unchanged.
Only the proved sufficient coefficient is adapted.

The 14 core entries are named top-level milestones, not an exact total of Lean
lemmas, source modules, analytic sublemmas, or audit declarations. S00-S06 below
are explicit support obligations. A theorem signature, arbitrary certificate
parameter, or an axiom-free conditional wrapper does not discharge them.

The previous nine endpoints E_1,...,E_9 are retained as aliases R1,...,R9 and
receive the stable global numbers E04,...,E12.

## 1. Normalization lock

Domain: T^3 = R^3/Z^3, unit-cube measure; identical Fourier coefficient array.
For real, solenoidal, mean-zero a set

    n(a)^2 = sum_{k != 0} (2*pi*|k|) * |a_hat(k)|^2,
    p(a)^2 = sum_{k != 0} |k| * |a_hat(k)|^2.

E01 must prove n(a)^2 = 2*pi*p(a)^2 and n(a) = sqrt(2*pi)*p(a).
It must also identify the order-3/2 energy and time normalization needed by
E02; changing the torus, volume convention, or coefficient normalization is
not permitted silently.

The proposed literature-to-native coefficient conversion is

    C_paper = K2 / sqrt(2),
    C_F     = K2 / (2*sqrt(pi)).

With A = n(u)^2, B = norm_native_HthreeHalf(u)^2:

    X = A/(4*pi), Y = B/(2*pi),
    X' + (nu-K2*sqrt(X))*Y <= 0
      <-> A' + 2*(nu-C_F*sqrt(A))*B <= 0.

The intended native radius is 2*sqrt(pi)*nu/K2; the corresponding coefficient
norm radius is sqrt(2)*nu/K2. K2 must be fixed by the actual literature
normalization and concrete proved Sobolev estimates. Defining a convenient
symbol named K2 does not establish that identification or E03.

## 2. Canonical endpoint register

| ID | Alias | Planned declaration | Exact role | Principal predecessors |
|---|---|---|---|---|
| E01 | N1 | FRONTIER_H12_NORM_BRIDGE | Coefficient/native Fourier norms and energy normalization | existing critical carrier and Parseval |
| E02 | N2 | FRONTIER_H12_CONSTANT_NORMALIZATION | Positive K2, native C_F, and exact ODI conversion | E01; explicit constant definitions |
| E03 | A1 | FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND | Actual finite NSE nonlinear bound with C_F | E01, E02, S00; proved Sobolev constant bundle |
| E04 | R1 | frontierGalerkinEnergyInvariant | E_1,N(t) <= n(a)^2 | E03, S01; generic invariant |
| E05 | R2 | frontierDissipationBudget | E_1,N(t)+2*delta_F*int E_3,N <= n(a)^2 | E04, S01; generic dissipation kernel |
| E06 | R3 | frontierSharpQuarticBudget | E_1,N(T)^2+4*delta_F*int E_2,N^2 <= E_1,N(0)^2 | E04, S01; interpolation and square-budget kernel |
| E07 | R4 | frontierTimeDerivativeBudget | Uniform L2 H^(-1/2) bound of the actual Galerkin RHS | E04, E05; existing negative transport bound |
| E08 | R5 | frontierPositiveTimeEnstrophyAccumulation | H1/H2 seed away from time zero | E06; cubic accumulation and actual enstrophy inequality |
| E09 | R6 | frontierPositiveTimeH2Bound | Integrated order-two seed on [tau,T] | E08; norm identities |
| E10 | R7 | frontierPositiveTimeAllOrders | Uniform all-order bounds on each positive-time interval | E09; generic high-order bootstrap |
| E11 | R8 | frontierLimitNegativeHalf | Negative-half RHS representative and frontier budget for the common limit | E07, S02, S03 |
| E12 | R9 | frontierLimitSharpQuartic | Joint terminal-energy/quartic Fatou budget for that same limit | E06, S02, S03 |
| E13 | C1 | FRONTIER_H12_NATIVE | Full native physical root with one common solution | E04-E12, S04-S06; existing physical/global kernels |
| E14 | C2 | FRONTIER_H12 | Literature-normalized public corollary | E01, E02, E13 |
| E15 | optional | FRONTIER_CONSTANT_LT_REPO_CONSTANT | C_F < C_repo, only if proved | E02; independently justified comparison |

Every entry is PLANNED. None is promoted by this organizational document.

## 3. Quantitative endpoint lock

Write n0 = n(a), delta_F = nu-C_F*n0 > 0. Let D_* be the existing proved
negative-half transport constant, not a relabeling of C_F.

    B_F(nu,a) = n0^2 / (2*delta_F),
    T_F(nu,a) = (nu+D_* n0)^2 * n0^2 / (2*delta_F),
    Q_F(nu,a) = n0^4 / (4*delta_F).

E03 must prove, for every cutoff and every supported, real, solenoidal c,

    |criticalNonlinearPower 1 N c|
      <= C_F * sqrt(criticalEnergy 1 N c) * criticalEnergy 3 N c.

The finite energy identity then supplies S01. E04-E07 export the invariant,
dissipation, retained-terminal quartic budget, and time-derivative bound.
E11-E12 concern the same extracted Galerkin limit, not separately chosen
solutions. E13 must retain strong Hhalf trace, n(u(t)) <= n0, global L2 HthreeHalf,
global L2 HminusHalf for the actual derivative, global L4 L6, physical NSE with
pressure, Leray-Hopf membership and the registered weak-strong uniqueness.
The budgets use B_F, T_F and delta_F; the original hardcoded repository-budget
denominators must not be substituted without a proved comparison.

## 4. Explicit support graph

S00: Define CriticalNonlinearCertificate(C) and fixed concrete Sobolev-constant
     data. An abstract certificate-parametric root is conditional until E03
     constructs the instance for C_F. No new global axiom is permitted.

S01: Derive the frontier differential inequality from E03 and the exact finite
     Galerkin energy identity. This is algebraic glue, not a second assumed
     nonlinear estimate.

S02: Apply CRITICAL_GALERKIN_GLOBAL_COMPACTNESS using E04, E05, E07 and the
     existing actual Galerkin family. Obtain one subsequence for all horizons.

S03: Construct local Bochner state/RHS representatives for S02 using E05/E07
     and the existing representative/limit machinery.

S04: Apply the existing strong critical trace theorem to S03. Preserve the
     actual initial coefficient array and its norm.

S05: Apply CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT to S02 and E10. Identify
     the positive-time physical flow with that same critical limit.

S06: Transfer E11/E12 to physical time derivatives and physical dissipation
     using S04/S05 and the existing Fourier identification/Fatou kernels.
     Complete global Bochner, Serrin and Leray-Hopf assembly for E13.

```text
E01 -> E02 -> E03 -> S01 -> E04
                           |      |
                           |      +-> E05 -> E07 --+
                           |      |               |
                           +------+-> E06         +-> S02 -> S03 -> S04
                                      |                   |       |
                                      +-> E08 -> E09 -> E10|       +-> E11
                                      |                   +-> E12 |
                                      +---------------------------+

(E10,S02) -> S05
(E11,E12,S04,S05) -> S06 -> E13 -> E14
E15 is separate from this root dependency chain.
```

The machine-readable edges in INDEX.json are authoritative where this compact
ASCII rendering suppresses shared predecessors.

## 5. Implementation tranches

T0: Preserve the original root/source hashes, compiler pin and Mathlib cache.
    Keep the older unrestricted-data AX6 root distinct from the small-data root.
T1: S00, E01, E02. Norm definitions, positivity, exact normalization and scalar
    bootstrap interfaces. No numerical gain is inferred by renaming constants.
T2: E03, S01. Prove the explicit Sobolev bundle and actual nonlinear estimate.
    Component/tensor factors and volume/frequency conventions are audited here.
T3: E04-E07. Instantiate generic invariant and budget kernels with C_F.
T4a: E08-E10, S05. Positive-time smoothing branch.
T4b: S02-S04, E11-E12. Compactness, strong trace and limit-budget branch.
T5: S06, E13, E14. One-solution physical assembly and both root audits.
T6: E15 when available; it is not a prerequisite for T1-T5.

Independent branches may elaborate asynchronously only after their dependency
bodies are validated. Pending signatures are not proved endpoints.

## 6. Source layout: planned, not created by reorganization

```text
SingularClosure/H12Frontier/
  Contracts.lean                 S00
  LiteratureConstants.lean       concrete constant data for E02/E03
  Normalization.lean             E01/E02
  NonlinearBound.lean            E03
  DifferentialInequality.lean    S01
  Invariant.lean                 E04
  Budgets.lean                   E05/E06
  TimeDerivative.lean            E07
  PositiveTime.lean              E08/E09/E10/S05
  Compactness.lean               S02/S03/S04
  Quantitative.lean              E11/E12 and physical transfer
  LerayHopf.lean                 S06 final physical assembly
  Root.lean                      E13/E14
  Closure.lean                   aggregate imports
  ConstantComparison.lean        optional E15
```

A source module may contain several milestones and auxiliary lemmas. Fourteen
core milestones is not a fourteen-file requirement. Existing base sources are
reused, not overwritten, and no BMO perturbation interface is added here.

## 7. Root semantics and comparison boundary

The existing theorem assumes C_repo*n0 < nu. For data satisfying only
C_F*n0 < nu, it cannot be invoked unless that old hypothesis is separately
proved. E13 therefore instantiates generic analytic kernels with C_F rather
than pretending to weaken the original theorem's premise.

C_repo is selected through Classical.choose from an existence theorem. Its
value is not automatically the particular witness written in that theorem's
proof. No comparison with K2 follows from the chosen notation.

E13/E14 may close independently of E15. A strict inclusion theorem over the
compiled repository ball additionally needs E15, both root certificates, and
a nonzero real solenoidal mean-zero datum providing an annulus witness.
Equality or the opposite order may instead be the relation eventually proved.

## 8. Verification and promotion

Retain the base run.cmd and base audit manifests. Add a separate cached native
Lean 4.33.0 frontier replay only when its sources exist. Its evidence must pin
the source snapshot, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, exact
root types, all declared premises, and theorem-level axiom output. Allowed
axioms remain propext, Classical.choice and Quot.sound. No sorryAx is allowed.

Base regression and frontier evidence are separate. The physical roots must
not retain an unproved Sobolev certificate, nonlinear estimate, convergence
admission, universal AX6 premise, or free K2 certificate. Prepared source is
at most A_TIER_CANDIDATE; only matching external evidence permits promotion.

This commit changes organization documents only. It performs no Lean run,
creates no Lean theorem, and adds no new mathematical certification.
