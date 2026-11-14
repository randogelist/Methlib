# H12_FRONTIER

**Branch:** `H12_extension`  
**Scope:** centered periodic unforced H^(1/2)_{sigma,0} coefficient adapter.  
**Frontier:** 14/14 milestones indexed; 0/14 completed at the recorded source pin.  
**Base:** historical unconditional small-data closure; separate from frontier verification.

## Assembly summary

[Download the summary TXT](FRONTIER_H12_ASSEMBLY_SUMMARY.txt) ·
[Endpoint register](index/ENDPOINTS.md) ·
[Native identities](index/BASE_IDENTITIES.md) ·
[Pinned Mathlib identities](index/MATHLIB_IDENTITIES.md)

The following block is identical to `FRONTIER_H12_ASSEMBLY_SUMMARY.txt`.

<!-- FRONTIER_H12_ASSEMBLY_SUMMARY_BEGIN -->
```text
FRONTIER_H12 — ASSEMBLY AND DEPENDENCY SUMMARY
============================================

REPOSITORY = randogelist/Methlib
BRANCH = H12_extension
PACKAGE = regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER
CANONICAL_THEOREM = FRONTIER_H12
NAMESPACE = SingularClosure.H12Frontier
SUMMARY_DATE = 2026-11-12
DOCUMENTATION_SOURCE_PIN = 33bfc91cec5a63ae49996a6b037f531a35e85ee8
LEAN = 4.33.0
MATHLIB = db584cd6d46c92f209a44c0f1c829460d327499d
CORE_MILESTONES = 14
REPLAY_MILESTONES = 9
OPTIONAL_COMPARISON_MILESTONES = 1
SUPPORT_WORK_PACKAGES = 7
MATHLIB_SOURCE_FAMILIES_INDEXED = 17
CORE_MILESTONES_INDEXED = 14/14
FRONTIER_MILESTONES_COMPLETED_AT_SOURCE_PIN = 0/14
SUMMARY_TYPE = SOURCE_INDEX_AND_ASSEMBLY_PLAN
NEW_COMPILER_OR_AXIOM_AUDIT_EVIDENCE = NONE
LOCAL_LEAN_EXECUTIONS = 0

1. SCOPE AND STATUS
-------------------

Target domain: unit three-torus T^3 = R^3/Z^3; unit-cube measure.
Equation: three-dimensional incompressible unforced Navier–Stokes.
Datum: real, solenoidal, mean-zero homogeneous H^(1/2).
Criterion retained: C_F * norm_native(a) < nu, with nu > 0.

The extension changes the sufficient centered smallness coefficient only.
The physical equation, viscosity, datum carrier, strong initial trace,
positive-time smoothness, and registered uniqueness class remain unchanged.
BMO^(-1), Beltrami, and a_dagger perturbation extensions are outside this scope.

Indexing is complete for the selected milestones. Implementation, concrete
constant identification, frontier replay, and matching external verification
remain distinct obligations. This summary is not a new mathematical derivation,
a Lean proof, or a compiler certificate.

2. IMMUTABLE BASE
-----------------

Base declaration:
  SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL

Base smallness:
  C_repo * norm_native(a) < nu,
  C_repo = SingularClosure.criticalNonlinearConstant.

Native definition:
  criticalNonlinearConstant = FINITE_CRITICAL_NONLINEAR_BOUND.choose.

Recorded original status: !!!! UNCONDITIONAL_CLOSURE.
Original source: 09dfe94a1ef150e21d09df3013fbe09002ef139c.
External cached workflow: 43059293572; job: 130657144029.
Local evidence locator: verification/h12-final-run.json.

The recorded base conclusion contains one global physical solution, strong
Hhalf initial trace, positive-time smoothness, global L2(HthreeHalf), global
L2(HminusHalf) for its actual derivative, global L4(L6), the quartic-gradient
budget, physical Leray–Hopf membership, and registered weak–strong uniqueness.

The copied base evidence is historical source-scoped evidence. It is not a
fresh compilation at H12_FRONTIER and does not complete a frontier milestone.
No equality or order between C_repo and a literature coefficient is inferred.

3. REGISTERED NORMALIZATION AND QUANTITATIVE TARGETS
---------------------------------------------------

For the same mean-zero Fourier coefficient array, define the intended norms:

  n(a)^2 = sum_(k != 0) (2*pi*|k|) * |a_hat(k)|^2,
  p(a)^2 = sum_(k != 0) |k| * |a_hat(k)|^2.

E01 target:
  n(a) = sqrt(2*pi) * p(a),
  with the corresponding order-3/2 energy identity.

Registered E02 conversion target:
  C_paper = K2/sqrt(2),
  C_F = K2/(2*sqrt(pi)),
  X = A/(4*pi), Y = B/(2*pi),
  X' + (nu - K2*sqrt(X))*Y <= 0
    <-> A' + 2*(nu - C_F*sqrt(A))*B <= 0.

Registered public radius: p(a) < sqrt(2)*nu/K2.
Registered native radius: n(a) < 2*sqrt(pi)*nu/K2.

These formulas require the actual literature conventions and concrete
Sobolev-constant certificates. A convenient definition named K2 does not
prove the literature identification or the nonlinear bound. Renaming the
native energy variable does not add a new sqrt(2) gain to the compiled base.

For n0 = n(a), set delta_F = nu - C_F*n0 > 0 and retain the separate proved
negative-half transport constant D_* = criticalTransportConstant.

  B_F = n0^2 / (2*delta_F),
  T_F = (nu + D_* n0)^2 * n0^2 / (2*delta_F),
  Q_F(T) = (n0^4 - n(u(T))^4) / (4*delta_F).

All limit and physical budgets must concern the same constructed solution.
Old C_repo-denominators cannot replace delta_F without a proved comparison.

4. FOURTEEN CORE MILESTONES
--------------------------

Native declarations below use namespace SingularClosure unless otherwise
specified. Native source paths and full declaration inventories are in
index/BASE_IDENTITIES.md. M01–M17 refer to Section 5.

E01 — FRONTIER_H12_NORM_BRIDGE
  Base: criticalSobolev_norm_sq;
        criticalFrequencyWeight_sq_of_ne_zero;
        criticalInitialPhysicalL2_fourierCoeff.
  Mathlib: M01, M02, M03 — Parseval, weighted lp sums, square roots.
  Remaining: exact order-1/2 and order-3/2 norm conversion, same coefficients
             and measure, removal of the modified zero weight by mean zero.

E02 — FRONTIER_H12_CONSTANT_NORMALIZATION
  Base: criticalEnergy_rate_split; GalerkinSolution.criticalEnergy_balance;
        criticalEnergyRate_inequality_of_nonlinear_bound.
  Mathlib: M03, M15, M13 — algebra, differentiation, integration.
  Remaining: concrete K2 data, positivity, and exact native ODI conversion.

E03 — FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND
  Base: criticalNonlinearPower_one_eq_physical;
        criticalNonlinearPower_one_enorm_le;
        FINITE_CRITICAL_HHALF_L3; FINITE_CRITICAL_DERIVATIVE_L3;
        criticalEnergy_interpolation_sqrt; critical_three_lines_midpoint.
  Mathlib: M05, M06, M11, M14, M01.
  Required endpoint:
    |criticalNonlinearPower 1 N c|
      <= C_F * sqrt(criticalEnergy 1 N c) * criticalEnergy 3 N c.
  Remaining: actual finite supported, real, solenoidal fields; concrete
             periodic scalar/vector/tensor estimates with combined constant
             at most C_F. Existential constants cannot be relabeled as C_F.
  Classification: principal fixed-coefficient analytic obligation.

E04 / R1 — frontierGalerkinEnergyInvariant
  Base: CRITICAL_ENERGY_INVARIANT;
        criticalGalerkin_criticalEnergy_initial_le.
  Mathlib: M04, M03.
  Remaining: instantiate the actual frontier ODI; obtain E_1,N(t) <= n0^2.

E05 / R2 — frontierDissipationBudget
  Base: CRITICAL_DISSIPATION_BUDGET;
        critical_uniform_dissipation_inequality.
  Mathlib: M13, M17.
  Remaining: E_1,N(t) + 2*delta_F*integral_0^t E_3,N <= n0^2.

E06 / R3 — frontierSharpQuarticBudget
  Base: CRITICAL_SQUARE_BUDGET_DIV; criticalEnergy_interpolation;
        criticalEnergy_two_eq_coefficientDissipation.
  Mathlib: M15, M14, M13.
  Remaining: retained terminal energy and the exact factor 4*delta_F.

E07 / R4 — frontierTimeDerivativeBudget
  Base: criticalFiniteSobolev_rhs_decomposition;
        criticalFiniteSobolev_laplacian_neg_one_norm;
        criticalFiniteSobolev_rhs_neg_one_bound.
  Mathlib: M02, M06, M13, M16.
  Remaining: actual Galerkin RHS bound in L2(HminusHalf) with budget T_F;
             retain D_* separately from C_F.

E08 / R5 — frontierPositiveTimeEnstrophyAccumulation
  Base: CUBIC_POSITIVE_TIME_ACCUMULATION;
        GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY.
  Mathlib: M10, M17, M04; M07 is only an alternative with restrictions.
  Remaining: insert n0^4/(4*delta_F) as the square budget and select an actual
             positive-time seed. No initial H1 bound is assumed.

E09 / R6 — frontierPositiveTimeH2Bound
  Base: SMALL_DATA_POSITIVE_TIME_H2_BOUND proof template;
        coefficientEnergy_le_dissipation; actual H2 energy decomposition.
  Mathlib: M13, M17.
  Remaining: replace the old seed invocation by E08, preserving an integrated
             H2 bound on every [tau,T] with tau > 0.

E10 / R7 — frontierPositiveTimeAllOrders
  Base: GALERKIN_POSITIVE_TIME_ALL_ORDERS;
        critical_positive_time_order_from_integrals;
        critical_shifted_linear_energy_budget.
  Mathlib: M10, M13, M17; M07 is not a direct variable-coefficient substitute.
  Remaining: supply E09; retain cutoff-uniform all-order positive-time bounds.

E11 / R8 — frontierLimitNegativeHalf
  Base: criticalGalerkinLimit_rhs_memLp;
        CRITICAL_GALERKIN_LOCAL_BOCHNER_REPRESENTATIVES;
        critical_negative_representative_physical.
  Mathlib: M08, M09, M16, M02; compactness support M12.
  Remaining: use the common limit, prove coefficient/physical derivative
             agreement, and transfer T_F. Domination is required only where
             a dominated-convergence theorem is actually invoked.

E12 / R9 — frontierLimitSharpQuartic
  Base: critical_modal_quartic_budget;
        criticalExtendedQuartic_le_liminf;
        critical_ennreal_liminf_add_le.
  Mathlib: M08, M03, M16.
  Remaining: joint terminal-energy and quartic Fatou passage for that same
             limit, with frontier coefficient 4*delta_F.

E13 — FRONTIER_H12_NATIVE
  Base: CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE;
        CRITICAL_GALERKIN_GLOBAL_COMPACTNESS_WITH_STRONG_TRACE;
        CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT;
        CRITICAL_POSITIVE_PHYSICAL_NSE;
        CriticalRegularSolution.global_energy_class;
        CriticalRegularSolution.serrin_global_memLp_of_quartic_budget;
        CriticalRegularSolution.lerayHopf_of_quartic;
        CriticalRegularSolution.lerayHopfUnique_of_serrin.
  Mathlib: M01, M08, M12, M16, M17, primarily through native wrappers.
  Remaining: one actual solution satisfying every registered quantitative,
             trace, pressure, smoothness, Leray–Hopf, and uniqueness field.
             Datumwise AX6 follows from the parameterized finite ODI budget;
             universal unrestricted-data AX6 is not an input.

E14 — FRONTIER_H12
  Dependencies: E01, E02, E13; Mathlib M03.
  Remaining: exact literature-normalized smallness conversion and E13
             application, with no change of carrier or physical conclusion.

5. PINNED MATHLIB SOURCE CATALOGUE
---------------------------------

Every source is relative to Mathlib/ at the fixed Mathlib commit above.
The JSON index records full names, blob hashes, and inspected source windows.

M01 Analysis/Fourier/AddCircleMulti.lean
    Fourier basis, Parseval, normalized torus/cube integration, reconstruction.
M02 Analysis/Normed/Lp/lpSpace.lean
    Memℓp.mono'; lp.norm_rpow_eq_tsum; summability and coefficient norms.
M03 Analysis/Real/Sqrt.lean
    Exact square-root algebra, positivity, and comparison.
M04 Analysis/Calculus/MeanValue.lean
    Right-derivative boundary comparison and scalar barriers.
M05 Analysis/FunctionalSpaces/SobolevInequality.lean
    Sobolev estimates with named constants; Hilbert-valued alternative.
M06 MeasureTheory/Function/LpSeminorm/CompareExp.lean
    Hölder, bilinear MemLp bounds, finite-measure exponent comparison.
M07 Analysis/ODE/Gronwall.lean
    Inspected constant-coefficient Grönwall inequalities.
M08 MeasureTheory/Integral/Lebesgue/Add.lean
    Fatou, directed monotone convergence, nonnegative integral operations.
M09 MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean
    Dominated convergence with an actual common integrable majorant.
M10 Topology/Order/Compact.lean
    IsCompact.exists_isMinOn for a seed on a compact time interval.
M11 Analysis/Complex/Hadamard.lean
    Hadamard three-lines theorem; already wrapped by the native package.
M12 Topology/ContinuousMap/Bounded/ArzelaAscoli.lean
    Equicontinuous families with a common compact range.
M13 MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean
    Integration of actual derivatives and derivative inequalities.
M14 Algebra/Order/BigOperators/Ring/Finset.lean
    Finite weighted Cauchy–Schwarz and interpolation.
M15 Analysis/Calculus/Deriv/Pow.lean
    Derivatives of squared and higher-power energies.
M16 MeasureTheory/Function/L1Space/Integrable.lean
    Norm moments, integrability, MemLp equivalence, a.e. representatives.
M17 MeasureTheory/Integral/IntervalIntegral/Basic.lean
    Interval translation, additivity, congruence, and halfline decomposition.

Applicability restrictions:
  Compact-support Euclidean Sobolev estimates require a periodic adapter.
  Hilbert-valued estimates do not automatically identify tensor/operator norms.
  Three-lines requires analyticity, strip boundedness, and boundary estimates.
  The inspected constant-K Grönwall theorem does not directly replace an
    integrated time-dependent coefficient argument.
  Arzelà–Ascoli does not make an infinite-dimensional bounded Hilbert ball compact.
  Fatou does not provide strong convergence or a common solution by itself.
  Dominated convergence requires a proved integrable majorant.
  Fourier Parseval does not alone identify fractional Sobolev conventions.

6. SUPPORT GRAPH AND ASSEMBLY ORDER
-----------------------------------

S00: certificate contract and concrete Sobolev-constant interfaces.
S01: actual finite frontier ODI obtained from E03 and the energy identity.
S02: one global Galerkin subsequence, using E04, E05, E07.
S03: compatible state/RHS Bochner representatives for that subsequence.
S04: strong Hhalf trace of the common limit.
S05: positive-time Sobolev/physical flow agreeing with that limit.
S06: physical quantitative transfer, global norms, and uniqueness assembly.

The combined compactness-with-strong-trace endpoint can shorten S02–S04;
it does not remove their required uniform budgets or coefficient agreement.

Assembly:
  S00 + E01 -> E02 -> E03 -> S01 -> E04
  E04 + S01 -> E05 and E06
  E04 + E05 -> E07
  E06 -> E08 -> E09 -> E10
  E04 + E05 + E07 -> S02 -> S03 -> S04
  E10 + S02 -> S05
  E07 + S02 + S03 -> E11
  E06 + S02 + S03 -> E12
  E11 + E12 + S04 + S05 -> S06
  E04–E12 + S04–S06 -> E13
  E01 + E02 + E13 -> E14

Preferred first tranche: S00, E01, E02.
Principal analytic tranche: E03, S01.
Replay: E04–E12; final common-solution assembly: E13–E14.

7. OPTIONAL COMPARISON
----------------------

E15 — FRONTIER_CONSTANT_LT_REPO_CONSTANT:
  C_F < C_repo.

E15 is not a prerequisite for an independently proved frontier root.
Strict enlargement of the compiled native ball additionally requires the
constant comparison and an admissible strict-inclusion witness. No such
comparison is supplied by the present indexing.

8. COMPLETION AND EXECUTION POLICY
----------------------------------

Per-milestone completion marker: !=!

Assignment requires all of:
  matching external cached compiler PASS;
  exact registered theorem-type PASS;
  theorem-level axiom audit PASS;
  allowed axioms only: propext, Classical.choice, Quot.sound;
  no sorryAx or unapproved axiom;
  no unresolved auxiliary analytic, certificate, checker, witness, or
    admission obligation.

Registered mathematical datum hypotheses remain unchanged.
An axiom-free conditional certificate wrapper is not a completed concrete
frontier milestone. Pending signatures are not proved bodies. Copied base
certificates do not promote new declarations.

No local Lean execution. Preserve the Lean 4.33.0 and Mathlib pins and reuse
cached dependencies; do not delete caches. External proof elaboration may be
scheduled independently before a deterministic final chain; theorem scopes,
premises, axioms, and endpoints must remain fixed.

This documentation update adds no Lean theorem, executes no compiler,
changes no base Lean source, and assigns no new !=! marker.

9. SOURCE REGISTER
-------------------

Package-relative authoritative records:
  index/ENDPOINTS.md
  index/INDEX.json
  index/BASE_IDENTITIES.md
  index/BASE_IDENTITIES.json
  index/MATHLIB_IDENTITIES.md
  index/MATHLIB_IDENTITIES.json
  verification/h12-final-run.json

Pinned project snapshot:
  https://github.com/randogelist/Methlib/tree/33bfc91cec5a63ae49996a6b037f531a35e85ee8/regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER

Pinned Mathlib snapshot:
  https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d

Historical base external verification:
  https://github.com/randogelist/Methlib/actions/runs/43059293572

The README summary block and FRONTIER_H12_ASSEMBLY_SUMMARY.txt contain the
same text. Historical copied-base documentation remains separately labeled.
```
<!-- FRONTIER_H12_ASSEMBLY_SUMMARY_END -->

## Historical copied-base documentation

The retained record below concerns the original base source and its external
verification. Its "extension modules" and audit counts belong to the base
closure, not the fourteen FRONTIER_H12 milestones. No fresh copied-path or
frontier compilation is asserted by this documentation update.

<details>
<summary>Original Singular-Axiomatic-closure README — retained verbatim</summary>

# Singular-Axiomatic-closure

**H^(1/2)_{sigma,0,small}: !!!! UNCONDITIONAL_CLOSURE.**

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

$$
\nu>0,\quad a\in\dot H^{1/2}_{\sigma,0}(\mathbb T^3),\quad
C_*\|a\|_{\dot H^{1/2}}<\nu
\quad\Longrightarrow\quad
\mathrm{AX6}_\nu(a)\ \land\ \mathrm{GlobalRegular}_\nu(a).
$$

Domain: unit three-torus. Forcing: zero. Initial trace: strong Hhalf.
Smoothness: positive time. Constants: C_*>0, c_*=C_*^(-1).
Additional analytic, certificate, or admission premises: none.

The same constructed solution satisfies global L2(H3half), global L2(HminusHalf)
for its actual positive-time derivative, global L4(L6), the sharp quartic-gradient
budget, actual physical Leray-Hopf membership, and uniqueness against every
member of the explicitly defined physical Leray-Hopf class with the same datum.

| Verification | Result |
|---|---|
| Exact full small-data root | PASS |
| Extension modules | 104/104 |
| Extension endpoint audits | 33/33 declarations; 27 audit modules |
| Original endpoint audit | 171/171 |
| Complete package build | PASS |
| Root axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Lean | 4.33.0; external cached GitHub Actions |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Local Lean executions | 0 |

Source commit: `09dfe94a1ef150e21d09df3013fbe09002ef139c`.
External evidence: [43059293572](https://github.com/randogelist/Methlib/actions/runs/43059293572).

- [Exact root](SingularClosure/NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean)
- [A-tier theorem and verification report](NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL_A_TIER.txt)
- [Verification manifest](verification/h12-final-run.json)
- [Stage ledger](H12_SMALL_STATUS.json)
- [Native cached replay](run.cmd)

## Frozen unrestricted-data root

**11/11 — !! A_TIER; !!! CONDITIONAL_FORMAL_CLOSURE.**

```lean
SingularClosure.ax6_implies_fefferman_B_0_adjust :
  AX6Statement → Fefferman_B_0_adjust
```

The universal `AX6Statement` remains an explicit unresolved premise of this
unrestricted-data implication. The small-data theorem discharges datumwise AX6
on its stated critical ball. It does not establish universal AX6.

| # | Frozen endpoint | Status |
|---:|---|---|
| 1 | `SIX_CHANNEL_PROJECTIONS` | !! A_TIER |
| 2 | `SIX_CHANNEL_ENSTROPHY_EQ` | !! A_TIER |
| 3 | `GALERKIN_GLOBAL_EXISTS_UNIQUE` | !! A_TIER |
| 4 | `GALERKIN_ENERGY_IDENTITY` | !! A_TIER |
| 5 | `GALERKIN_ENSTROPHY_INEQUALITY` | !! A_TIER |
| 6 | `CUBIC_ENERGY_OF_SQUARE_BUDGET` | !! A_TIER |
| 7 | `AX6_UNIFORM_STRONG_BOUNDS` | !! A_TIER |
| 8 | `GALERKIN_GLOBAL_STRONG_LIMIT` | !! A_TIER |
| 9 | `GLOBAL_STRONG_SMOOTH_BOOTSTRAP` | !! A_TIER |
| 10 | `PERIODIC_PRESSURE_RECOVERY` | !! A_TIER |
| 11 | `ax6_implies_fefferman_B_0_adjust` | !! A_TIER |

[Original endpoint ledger](ENDPOINTS.json).
Historical correction/review files record earlier source checkpoints; the
verification manifest above specifies the current small-data source and audit.

## Native Windows replay

```cmd
call run.cmd
```

Pinned Lean and Mathlib; cached dependencies preserved; full source build;
33 extension exact-type/axiom checks; original 171-declaration audit.


</details>
