# FRONTIER_H12: base-identity map for E01--E14

```text
BRANCH=H12_extension
SOURCE_PIN=e678fba2a6e676a011c3019032c92b91ea78d2e4
PACKAGE=regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER
CORE_MILESTONES=14
UNCONDITIONALLY_COMPLETED_FRONTIER_MILESTONES=0
NEW_LEAN_SOURCE=NONE
LOCAL_LEAN_EXECUTIONS=0
```

Scope: identify existing mathematical/Lean dependencies for the centered Hhalf coefficient adapter. This is a source map, not a new proof or compiler certificate. The reviewed sources are the native copied package and the explicitly identified Methlib pkg1/pkg2 files. No exhaustive claim about all other GitHub repositories is made.

## Completion marker

The requested per-milestone marker is `!=!`.

A milestone receives it only after its exact registered declaration has a matching external cached compiler PASS, an exact-type check, a theorem-level axiom audit allowing only `propext`, `Classical.choice`, `Quot.sound`, and no unresolved auxiliary analytic, certificate, checker, witness, or admission obligation. Mathematical datum hypotheses in the registered theorem remain unchanged.

A generic theorem conditional on an unproved frontier nonlinear certificate does not complete the corresponding concrete milestone. An existing base theorem does not automatically mark its frontier specialization complete. The original base record remains distinct from the fourteen new milestones.

Source pin: [e678fba2](https://github.com/randogelist/Methlib/commit/e678fba2a6e676a011c3019032c92b91ea78d2e4).
Original base evidence: [verification/h12-final-run.json](../verification/h12-final-run.json), source `09dfe94a1ef150e21d09df3013fbe09002ef139c`, run `43059293572`, job `130657144029`. The job step summaries were re-read: cached dependencies, compilation, extension audit, exact-root check and original-endpoint check report success. This is historical base evidence, not a new frontier run or an independent individual audit of every helper listed below.

## Reuse classes

- `DIRECT`: coefficient-independent or parameterized kernel; its explicit premises still have to be supplied.
- `REPLAY`: existing proof template hardcodes `criticalNonlinearConstant`; adapt the proof, not the old smallness hypothesis.
- `CANDIDATE`: cross-package source inspected; carrier, import and matching audit compatibility require separate verification before adoption.

Unless another namespace is written explicitly, declarations below are in `SingularClosure`. Source paths are relative to the native package. All reviewed base Lean files remain unchanged.

## E01 -- FRONTIER_H12_NORM_BRIDGE

**DIRECT sources:**

- [CriticalSpaces.lean](../SingularClosure/CriticalSpaces.lean): `criticalSobolev_norm_sq`, `criticalFrequencyWeight_sq_of_ne_zero`, `criticalFrequencyWeight_pos`, `criticalHalfWeight_sq`.
- [CriticalInitialPhysicalFourier.lean](../SingularClosure/CriticalInitialPhysicalFourier.lean): `criticalInitialPhysicalL2_fourierCoeff`, `criticalInitialPhysicalL2_norm`, `criticalInitialPhysicalL2_norm_sq`.
- [CriticalInitialEnergy.lean](../SingularClosure/CriticalInitialEnergy.lean): `criticalEnergy_le_norm_sq`, `criticalGalerkin_criticalEnergy_initial_le`.

**Existing identity:** the native squared norm is the sum of the actual frequency weight times the squared Fourier coefficients. Fourier recovery fixes the physical representative independently of smallness.

**Remaining derivation:** define the literature coefficient norm on the same real, solenoidal, mean-zero carrier; prove the order-1/2 and order-3/2 normalization equalities. The modified weight at k=0 must be removed using the mean-zero premise. Preserve unit-cube measure and the actual Fourier coefficients.

**Optional CANDIDATE:** `regularity-B-assembly/pkg2/CEA07F_TorusStokesQuarter.lean`, namespace `CEATheta`: `torus3StokesEigenvalue`, `torus3StokesEigenvalue_nonneg`, `torus3_l2_spectral_eq_physical`, `torus3_stokes_quarter_dictionary`. This is a finite physical/spectral dictionary on another carrier, not the required infinite native norm bridge.

## E02 -- FRONTIER_H12_CONSTANT_NORMALIZATION

**DIRECT sources:**

- E01's frequency/norm equalities.
- [CriticalEnergy.lean](../SingularClosure/CriticalEnergy.lean): `criticalEnergyRate`, `criticalEnergy_rate_split`, `GalerkinSolution.criticalEnergy_balance`.
- [SmallDataAX6.lean](../SingularClosure/SmallDataAX6.lean): `criticalEnergyRate_inequality_of_nonlinear_bound`.
- Pinned Mathlib square-root identities already used by the base: `Real.sqrt_mul`, `Real.sq_sqrt`, `Real.sqrt_sq`.

**Remaining derivation:** define and justify the fixed literature constants and all volume/component conventions; prove their positivity and the exact scalar conversion. The currently registered target is `C_F = K2/(2*sqrt(pi))` in native coordinates, with `X=A/(4*pi)` and `Y=B/(2*pi)`. These are targets to prove, not existing imported endpoints.

The native base already uses squared norm A and the coefficient `2*(nu-C*sqrt(A))`. Merely renaming A/2 does not provide an additional sqrt(2) gain over the repository theorem. No equality between `criticalNonlinearConstant` and a literature expression is established by this map.

## E03 -- FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND

**DIRECT sources:**

- [CriticalEnergy.lean](../SingularClosure/CriticalEnergy.lean): `criticalNonlinearPower_one_eq_physical`, `FINITE_CRITICAL_LAMBDA_PARSEVAL`, `criticalEnergy_derivative_sum`.
- [CriticalHolder.lean](../SingularClosure/CriticalHolder.lean): `finite_criticalLambda_eLpNorm_two`, `criticalNonlinearPower_one_enorm_le`, `finite_critical_derivative_L3_of_component_bound`.
- [CriticalSobolev.lean](../SingularClosure/CriticalSobolev.lean): `FINITE_CRITICAL_HHALF_L3`, `CRITICAL_COMPLEX_FINITE_L3`, `critical_complex_lpNorm_three_bound`.
- [CriticalNonlinear.lean](../SingularClosure/CriticalNonlinear.lean): `FINITE_CRITICAL_DERIVATIVE_L3`, `ennreal_critical_holder_product`.
- [CriticalFourierInterpolation.lean](../SingularClosure/CriticalFourierInterpolation.lean): `criticalEnergy_interpolation`, `criticalEnergy_interpolation_sqrt`.

**REPLAY source:** `FINITE_CRITICAL_NONLINEAR_BOUND` in `CriticalNonlinear.lean`. It combines an L6 constant and a derivative-L3 constant, proves the intermediate product bound, and finally selects a positive constant with added slack. It does not export the required fixed C_F.

**Remaining derivation:** export the constant-explicit product compiler and establish concrete bounds whose combined native coefficient is at most C_F. Track scalar/vector/matrix norms and the explicit factor 3 in the current component-to-derivative estimate. Do not identify existentially selected constants with the literature constants by notation.

**Optional CANDIDATE:** `regularity-B-assembly/pkg1/H12_CRITICAL_TRILINEAR_COMPILER.lean`, namespace `H12CriticalTrilinearCompiler`: `critical_trilinear`, `critical_energy_absorbed`, `H12_CRITICAL_TRILINEAR_COMPILER`. The first proves `Iabs <= C3^3*E*D^2` from explicit `PeriodicHhalfL3` and `CriticalHolder` premises. Those premises and the comparison with C_F must still be discharged. This alternative L3-L3-L3 compiler is not an unconditional proof of E03.

## E04 / R1 -- frontierGalerkinEnergyInvariant

**DIRECT sources:**

- [CriticalInvariant.lean](../SingularClosure/CriticalInvariant.lean): `scalar_invariant_of_deriv_nonpos_below`, `CRITICAL_ENERGY_INVARIANT`.
- [CriticalInitialEnergy.lean](../SingularClosure/CriticalInitialEnergy.lean): `criticalGalerkin_criticalEnergy_initial_le`.
- [CriticalEnergy.lean](../SingularClosure/CriticalEnergy.lean): `GalerkinSolution.criticalEnergy_balance`, `GalerkinSolution.criticalEnergy_continuousOn`.
- [SmallDataAX6.lean](../SingularClosure/SmallDataAX6.lean): `criticalEnergyRate_inequality_of_nonlinear_bound`.

**Remaining derivation:** instantiate C=C_F, a0=norm(a), and the actual finite trajectory; discharge the differential premise using E03/S01. Result: `E1_N(t) <= norm(a)^2`. The scalar invariant itself is not missing.

## E05 / R2 -- frontierDissipationBudget

**DIRECT sources:**

- [CriticalDissipation.lean](../SingularClosure/CriticalDissipation.lean): `CRITICAL_DISSIPATION_BUDGET`.
- [CriticalInvariant.lean](../SingularClosure/CriticalInvariant.lean): `critical_uniform_dissipation_inequality`.
- [CriticalUniformBounds.lean](../SingularClosure/CriticalUniformBounds.lean): `GalerkinSolution.criticalState_norm_sq_nat`.

**Remaining derivation:** use the same trajectory and `delta_F=nu-C_F*norm(a)>0`; convert finite energy to the actual CriticalSobolev-3 state norm. Retain `E1_N(t)+2*delta_F*integral(E3_N)<=norm(a)^2` and export `B_F=norm(a)^2/(2*delta_F)`.

Do not reuse `criticalDissipationBudget` as the frontier definition: it hardcodes the old repository coefficient.

## E06 / R3 -- frontierSharpQuarticBudget

**DIRECT sources:**

- [CriticalInvariant.lean](../SingularClosure/CriticalInvariant.lean): `CRITICAL_SQUARE_BUDGET`, `CRITICAL_SQUARE_BUDGET_DIV`.
- [CriticalFourierInterpolation.lean](../SingularClosure/CriticalFourierInterpolation.lean): `criticalEnergy_interpolation`, `criticalEnergy_two_eq_coefficientDissipation`, `coefficientDissipation_sq_le_criticalEnergy`.
- [SmallDataAX6.lean](../SingularClosure/SmallDataAX6.lean): `GalerkinSolution.critical_square_budget_of_differential_inequality`, `GalerkinSolution.critical_budget6_of_differential_inequality`.

**Remaining derivation:** instantiate C_F and retain the terminal energy. Use `CRITICAL_SQUARE_BUDGET` for the exact finite initial energy, before weakening it to norm(a)^4. The six-channel conversion is already parameterized and supplies datumwise AX6 without any universal AX6 assumption.

## E07 / R4 -- frontierTimeDerivativeBudget

**DIRECT sources:**

- [CriticalTimeDerivative.lean](../SingularClosure/CriticalTimeDerivative.lean): `criticalFiniteSobolev_rhs_decomposition`, `criticalFiniteSobolev_laplacian_neg_one_norm`, `criticalFiniteSobolev_rhs_neg_one_bound`, `criticalTransportConstant_bound`, `criticalTransportConstant_pos`.
- [CriticalFourierInterpolation.lean](../SingularClosure/CriticalFourierInterpolation.lean): `criticalEnergy_interpolation_sqrt`.

**REPLAY source:** `CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET` in `CriticalTimeDerivative.lean`.

**Remaining derivation:** combine the coefficient-independent pointwise RHS bound with E04 and E05, obtaining `T_F=(nu+D_*norm(a))^2*norm(a)^2/(2*delta_F)`. Keep D_*=`criticalTransportConstant`; there is no reason to replace it by C_F. The old integrated theorem cannot be applied with the enlarged smallness hypothesis unchanged.

## E08 / R5 -- frontierPositiveTimeEnstrophyAccumulation

**DIRECT sources:**

- [CriticalPositiveTimeScalar.lean](../SingularClosure/CriticalPositiveTimeScalar.lean): `continuous_exists_point_le_integral_bound`, `CUBIC_POSITIVE_TIME_ACCUMULATION`.
- [EnstrophyAbsorption.lean](../SingularClosure/EnstrophyAbsorption.lean): `GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY`.
- [StrongAccumulation.lean](../SingularClosure/StrongAccumulation.lean): `coefficientEnstrophyRate`, `GalerkinSolution.coefficientEnstrophyRate_continuousOn`, `GalerkinSolution.coefficientLaplacianSquare_continuousOn`.

**REPLAY source:** `SMALL_DATA_POSITIVE_TIME_ENSTROPHY_ACCUMULATION` in [CriticalPositiveTimeSeed.lean](../SingularClosure/CriticalPositiveTimeSeed.lean).

**Remaining derivation:** supply E06's `M_F=norm(a)^4/(4*delta_F)` to the scalar accumulation theorem. Obtain the explicit positive-time bound `sqrt(M_F/tau)*exp(kappa*M_F)`. Initial H1 or H2 regularity is not assumed.

## E09 / R6 -- frontierPositiveTimeH2Bound

**REPLAY source:** [CriticalPositiveTimeSeed.lean](../SingularClosure/CriticalPositiveTimeSeed.lean): `SMALL_DATA_POSITIVE_TIME_H2_BOUND`.

**Existing identities used in that proof:** `highOrderEnergy_eq_sobolev_norm_sq`, `GalerkinSolution.sobolevState_H2_square_eq`, `GalerkinSolution.physicalH2Square_eq`, `coefficientEnergy_le_dissipation`. Their use is explicit in the source template; this sentence identifies the use site rather than claiming all are declared in that file.

**Remaining derivation:** replace the invocation of the old small-data accumulation theorem by E08. From `E0<=E2` and `H2_inhom^2=E0+2*E2+E4`, the same proof yields an integrated seed bounded by `3*L_F*(T-tau)+L_F/nu`. No new Sobolev embedding is required at this milestone.

## E10 / R7 -- frontierPositiveTimeAllOrders

**DIRECT sources:**

- [CriticalPositiveTimeHighOrder.lean](../SingularClosure/CriticalPositiveTimeHighOrder.lean): `critical_positive_time_order_from_integrals`, `GALERKIN_POSITIVE_TIME_ALL_ORDERS`.
- [CriticalPositiveTimeEnergy.lean](../SingularClosure/CriticalPositiveTimeEnergy.lean): `critical_exists_energy_le_average`, `critical_shifted_linear_energy_budget`.

**REPLAY source:** `SMALL_DATA_POSITIVE_TIME_ALL_ORDERS`.

**Remaining derivation:** provide E09 as the generic `hseed`, keeping uniformity over actual Galerkin trajectories and cutoffs. The all-order induction is already proved. Retain the integrated next-order bound, not only a pointwise norm bound.

## E11 / R8 -- frontierLimitNegativeHalf

**DIRECT sources:**

- [CriticalLimitRepresentatives.lean](../SingularClosure/CriticalLimitRepresentatives.lean): `criticalGalerkinLimit_rhs_memLp`, `CRITICAL_GALERKIN_LOCAL_BOCHNER_REPRESENTATIVES`.
- [CriticalPhysicalQuantitative.lean](../SingularClosure/CriticalPhysicalQuantitative.lean): `critical_negative_representative_physical`, `CriticalPositiveSobolevFlow.timeDerivative_fourierCoeff`.

**REPLAY source:** `SMALL_DATA_LIMIT_NEGATIVE_HALF` in `CriticalQuantitative.lean`.

**Remaining derivation:** specialize q=-1 and budget T_F on the common subsequence from S02. The source theorem already returns actual coefficient agreement with `fullFourierRhs`. After S05, transfer this to the actual physical time derivative. Do not select an unrelated solution.

## E12 / R9 -- frontierLimitSharpQuartic

**DIRECT source:** [CriticalQuantitative.lean](../SingularClosure/CriticalQuantitative.lean): `critical_modal_quartic_budget`, `criticalExtendedQuartic_le_liminf`, `critical_ennreal_liminf_add_le`, `critical_ennreal_liminf_mul_le`, `critical_ofReal_square_square`.

**REPLAY source:** `SMALL_DATA_LIMIT_SHARP_QUARTIC` in the same file.

**Remaining derivation:** insert E06 with coefficient `4*delta_F` into the joint terminal-energy/time-integral Fatou theorem, on the same limit as E11. Preserve the terminal term. Strong critical convergence at the terminal time is not an extra premise of this passage.

## E13 -- FRONTIER_H12_NATIVE

**DIRECT construction and realization sources:**

- [CriticalGalerkin.lean](../SingularClosure/CriticalGalerkin.lean): `CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE`, `criticalGalerkinSolution`, `criticalGalerkinSolution_initial`.
- [CriticalTraceClosure.lean](../SingularClosure/CriticalTraceClosure.lean): `CRITICAL_GALERKIN_GLOBAL_COMPACTNESS_WITH_STRONG_TRACE`, `CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE_OF_BUDGETS`.
- [CriticalPositiveLimit.lean](../SingularClosure/CriticalPositiveLimit.lean): `CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT`.
- [CriticalPositiveFlow.lean](../SingularClosure/CriticalPositiveFlow.lean): `CRITICAL_POSITIVE_PHYSICAL_NSE`.
- [CriticalGlobalEnergyClass.lean](../SingularClosure/CriticalGlobalEnergyClass.lean): `CriticalRegularSolution.global_energy_class`.
- [CriticalGlobalSerrin.lean](../SingularClosure/CriticalGlobalSerrin.lean): `CriticalRegularSolution.serrin_global_memLp_of_quartic_budget`.
- [CriticalStrongLerayHopf.lean](../SingularClosure/CriticalStrongLerayHopf.lean): `CriticalRegularSolution.lerayHopf_of_quartic`.
- [SmallDataUniqueness.lean](../SingularClosure/SmallDataUniqueness.lean): `CriticalRegularSolution.lerayHopfUnique_of_serrin`.

**REPLAY templates:** `SMALL_DATA_CRITICAL_QUANTITATIVE_REGULARITY` in `SmallDataQuantitative.lean`, and `NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL` in `NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean`.

**Remaining derivation:** construct one `CriticalRegularSolution` from E04--E12 and S00--S06; supply frontier, not old, budget denominators. Reuse the physical/uniqueness methods on that same object. Include datumwise AX6 via the generic finite six-channel budget. Calling the old root cannot establish the new root unless a separately proved constant comparison makes its old hypothesis available.

## E14 -- FRONTIER_H12

**DIRECT inputs:** E01, E02 and E13, with unchanged `CriticalSigmaZero` and physical conclusion. Existing native carrier: [CriticalRegularityContracts.lean](../SingularClosure/CriticalRegularityContracts.lean).

**Remaining derivation:** prove that the literal literature-normalized smallness premise implies E13's native premise, then apply E13. No additional PDE estimate is required. An alternative invocation of the original root is valid only after proving `C_repo <= C_F`; no such comparison is supplied by this map.

## Support identities S00--S06

| Support | Existing source/identity | Remaining interface |
|---|---|---|
| S00 | `FINITE_CRITICAL_NONLINEAR_BOUND` and `criticalNonlinearConstant_bound` provide the contract model | Define an explicit frontier certificate with all analytical obligations visible; E03 must construct it |
| S01 | `criticalEnergyRate_inequality_of_nonlinear_bound`; actual `criticalEnergy_balance` | Specialize with E03 |
| S02 | `CRITICAL_GALERKIN_GLOBAL_COMPACTNESS`; stronger combined endpoint `CRITICAL_GALERKIN_GLOBAL_COMPACTNESS_WITH_STRONG_TRACE` | Insert E04/E05/E07 and preserve one subsequence |
| S03 | `criticalGalerkinLimit_state_memLp`, `criticalGalerkinLimit_rhs_memLp`, `CRITICAL_GALERKIN_LOCAL_BOCHNER_REPRESENTATIVES` | Insert B_F and T_F |
| S04 | `CRITICAL_HHALF_STRONG_TRACE`; `CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE_OF_BUDGETS` | Fix the same initial coefficient array; can share the combined S02 endpoint |
| S05 | `CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT`; `CRITICAL_POSITIVE_PHYSICAL_NSE` | Supply E10 bounds and agreement with S02's limit |
| S06 | `critical_negative_representative_physical`; `critical_smooth_extendedSquare_eq_dissipation`; the four `CriticalRegularSolution` methods listed under E13 | Generalize the old fixed-coefficient physical-quartic wrapper, then build global bounds and uniqueness for one U |

Combining S02 and S04 through the stronger existing theorem changes scheduling, not the theorem or its premises.

## Optional comparison E15

[SmallDataAX6Closure.lean](../SingularClosure/SmallDataAX6Closure.lean) defines `criticalNonlinearConstant := FINITE_CRITICAL_NONLINEAR_BOUND.choose` and proves positivity and the corresponding bound. These identities do not prove equality or either order relation with C_F. E15 remains outside the fourteen core milestones and is required only for a strict comparison with the existing compiled native ball.

## Import and verification boundary

All primary identities above already belong to the copied native package. The two cross-package candidates remain optional; do not introduce parent-relative package imports or silently switch carriers. No heat/BMO/helical machinery is needed for this centered-coefficient assembly.

The source inventory is not a compiler audit. All E01--E14 completion markers remain unset. The JSON companion records exact source names, reuse classes, and remaining obligations. No source file, theorem statement, old certificate, cache, toolchain pin or base runner is changed by this map.
