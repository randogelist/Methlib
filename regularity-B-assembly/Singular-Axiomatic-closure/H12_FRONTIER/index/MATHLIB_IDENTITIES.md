# FRONTIER_H12: pinned Mathlib identity map

```text
BRANCH=H12_extension
METHLIB_SOURCE_PIN=3ce4067a7ea3a6f39c92b8faf4bcf51cf1c8a42d
MATHLIB_SOURCE_PIN=db584cd6d46c92f209a44c0f1c829460d327499d
LEAN=4.33.0
CORE_MILESTONES_INDEXED=14/14
MATHLIB_SOURCE_FAMILIES=17
FRONTIER_MILESTONES_COMPLETED=0/14
LOCAL_LEAN_EXECUTIONS=0
NEW_THEOREM_PROMOTIONS=0
```

Companion machine-readable register: [MATHLIB_IDENTITIES.json](MATHLIB_IDENTITIES.json).
Existing native dependencies: [BASE_IDENTITIES.md](BASE_IDENTITIES.md).
Exact milestone scope: [ENDPOINTS.md](ENDPOINTS.md).

## Evidence and scope

The named library declarations below were inspected in source at the pinned Mathlib commit. The companion register records source paths, blob hashes and reviewed source-line windows. Current-branch search results were used only for discovery, not as evidence of pinned availability. This is a targeted source survey, not an exhaustive search of all Mathlib or a new compiler audit.

A source identity is not a completed frontier milestone. `!=!` remains reserved for the exact registered concrete endpoint after matching external cached compilation, exact-type checking, standard-only theorem-level axiom audit, and discharge of its auxiliary analytic obligations. No new completion marker is assigned here.

`DIRECT` denotes an applicable generic lemma after its explicit hypotheses are supplied. `WRAPPED` denotes library machinery already organized by a native Methlib theorem; prefer the native wrapper. `ADAPTER` denotes a required carrier, domain, norm or quantitative bridge. `ALTERNATIVE` is not a drop-in replacement for the existing theorem.

## Source catalogue

Every linked file is pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`. Exact declarations and source hashes are registered in the JSON.

| ID | Mathlib source | Principal role |
|---|---|---|
| M01 | [Analysis/Fourier/AddCircleMulti](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Fourier/AddCircleMulti.lean) | normalized torus Fourier basis, Parseval, reconstruction |
| M02 | [Analysis/Normed/Lp/lpSpace](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Normed/Lp/lpSpace.lean) | weighted coefficient carriers and norm sums |
| M03 | [Analysis/Real/Sqrt](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Real/Sqrt.lean) | exact square-root normalization and barriers |
| M04 | [Analysis/Calculus/MeanValue](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/MeanValue.lean) | right-derivative comparison fences |
| M05 | [Analysis/FunctionalSpaces/SobolevInequality](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean) | compact-support Sobolev estimates with named constants |
| M06 | [MeasureTheory/Function/LpSeminorm/CompareExp](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean) | bilinear Holder and exponent comparison |
| M07 | [Analysis/ODE/Gronwall](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/ODE/Gronwall.lean) | constant-coefficient comparison, conditional uniqueness tools |
| M08 | [MeasureTheory/Integral/Lebesgue/Add](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean) | Fatou, monotone convergence and nonnegative sums |
| M09 | [MeasureTheory/Integral/Lebesgue/DominatedConvergence](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean) | dominated cutoff-tail passage |
| M10 | [Topology/Order/Compact](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Order/Compact.lean) | minimum/averaging seed times |
| M11 | [Analysis/Complex/Hadamard](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Complex/Hadamard.lean) | fractional Sobolev interpolation machinery |
| M12 | [Topology/ContinuousMap/Bounded/ArzelaAscoli](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean) | common-limit compactness support |
| M13 | [MeasureTheory/Integral/IntervalIntegral/FundThmCalculus](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean) | integrate finite Galerkin differential estimates |
| M14 | [Algebra/Order/BigOperators/Ring/Finset](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean) | finite Cauchy-Schwarz with constant one |
| M15 | [Analysis/Calculus/Deriv/Pow](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Deriv/Pow.lean) | differentiate squared critical energy |
| M16 | [MeasureTheory/Function/L1Space/Integrable](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean) | finite norm moments, MemLp, representative transfer |
| M17 | [MeasureTheory/Integral/IntervalIntegral/Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean) | interval splitting, translation and exhaustion bookkeeping |

## E01 -- FRONTIER_H12_NORM_BRIDGE

M01/M02/M03; DIRECT and WRAPPED.

Use `UnitAddTorus.hasSum_sq_mFourierCoeff`, `UnitAddTorus.mFourierBasis_repr`, `UnitAddTorus.integral_preimage`, `lp.norm_rpow_eq_tsum` and `Memℓp.mono'`, with `Real.sq_sqrt` / `Real.sqrt_sq`.

The native wrapper remains `criticalSobolev_norm_sq` with the actual physical Fourier recovery lemmas. The library torus uses probability Haar measure. The required order-1/2 and order-3/2 coefficient/native norm equalities still need to be proved on the same real, solenoidal, mean-zero carrier. Parseval alone does not identify the Sobolev weight or the literature convention.

## E02 -- FRONTIER_H12_CONSTANT_NORMALIZATION

M03/M15/M13; DIRECT scalar support.

`Real.sqrt_eq_iff_eq_sq`, `Real.sq_sqrt`, `Real.sqrt_sq` and `Real.sqrt_pos` handle the algebraic coefficient conversion. Derivative/FTC identities support energy normalization. The concrete K2 definition and Sobolev-constant bundle are separate project inputs to establish, not Mathlib theorem names.

Do not identify C_repo, K2, and C_F by notation. No extra sqrt(2) enlargement of the native repository criterion follows from rewriting A as 2X.

## E03 -- FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND

M05/M06/M11/M14/M01; ADAPTER plus WRAPPED generic inequalities.

Verified analytic tools:

- `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner` and `MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst`;
- `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` and `MeasureTheory.SNormLESNormFDerivOfEqConst`;
- `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm`;
- `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`;
- `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`.

The Sobolev theorem supplies a compact-support first-order estimate on a finite-dimensional normed domain with Haar measure. In dimension three, p=2 and p'=6 satisfy the exponent equation. This is not already the periodic fractional Hhalf-to-L3 inequality, and its named constant is not automatically the literature C_S.

The inner-product-codomain version is a useful quantitative candidate: it avoids the extra arbitrary-codomain norm-equivalence factors present in `SNormLESNormFDerivOfEqConst`. This does not by itself prove a smaller periodic constant. For tensor-valued inputs, the Hilbert tensor norm and the actual derivative operator norm must be related explicitly.

Holder can instantiate the 6,3,2 product estimate and then the 2,2,1 pairing estimate, after actual pointwise convection and measurability hypotheses are supplied. Three-lines gives the midpoint product sqrt(A)*sqrt(B) after an analytic strip family, closed-strip boundedness and both boundary estimates have been proved.

Methlib already implements the last analytic reduction as `critical_three_lines_midpoint` in `CriticalSobolevAnalytic.lean`; prefer that wrapper. The library's finite Cauchy-Schwarz inequality already underlies `criticalEnergy_interpolation`.

Outstanding: concrete periodic scalar/vector/tensor estimates whose combined coefficient is at most the fixed C_F. None of the inspected Mathlib declarations discharges this exact comparison.

## E04 / R1 -- frontierGalerkinEnergyInvariant

M04/M03; WRAPPED.

`image_le_of_deriv_right_lt_deriv_boundary` and `image_le_of_deriv_right_le_deriv_boundary` supply comparison fences. The existing `CRITICAL_ENERGY_INVARIANT` already adapts these to the strict critical gap. Supply E03's actual Galerkin differential inequality and preserve the right-derivative-at-zero convention. A comparison theorem is not itself a PDE existence theorem.

## E05 / R2 -- frontierDissipationBudget

M13/M17; WRAPPED.

Use `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le` and interval additivity as lower-level support for the existing `CRITICAL_DISSIPATION_BUDGET`.

Continuity, derivative and interval-integrability premises apply to the finite Galerkin energies. Preserve the factor 2*(nu-C_F*n0); do not transplant an old C_repo denominator.

## E06 / R3 -- frontierSharpQuarticBudget

M15/M14/M13; WRAPPED.

`HasDerivWithinAt.fun_pow` and `HasDerivAt.pow` differentiate A^2. `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` gives E2^2 <= E1*E3. Combined with the dissipation inequality, these yield the coefficient 4*(nu-C_F*n0).

Reuse `CRITICAL_SQUARE_BUDGET` / `CRITICAL_SQUARE_BUDGET_DIV`; retain the terminal critical energy. The exact NSE identity is still supplied by Methlib, not by a generic differentiation lemma.

## E07 / R4 -- frontierTimeDerivativeBudget

M02/M06/M13/M16; WRAPPED.

`Memℓp.mono'` supports weighted coefficient domination. `MeasureTheory.MemLp.of_bilin` and Holder provide generic product integrability. `MeasureTheory.MemLp.integrable_norm_pow` converts L2 membership to an integrable square, with the nonzero exponent premise.

Prefer the existing actual negative-half RHS decomposition and bound. The derivative estimate is a conclusion from those physical Fourier identities plus E04/E05; it must not be inserted as an extra certificate. Preserve the separate transport constant D_*.

## E08 / R5 -- frontierPositiveTimeEnstrophyAccumulation

M10/M17/M04; WRAPPED. M07 is an ALTERNATIVE only.

`IsCompact.exists_isMinOn` supplies a seed time on [0,tau] after continuity and nonemptiness. Interval translation/additivity transfers the evolution estimate to the seed interval. Reuse `CUBIC_POSITIVE_TIME_ACCUMULATION` with the frontier quartic budget.

The inspected Mathlib Gronwall statements use a constant K. They do not directly replace Methlib's estimate using the integral of a time-dependent coefficient. In particular, a bound on the norm of a derivative is not interchangeable with a signed dissipative energy inequality.

## E09 / R6 -- frontierPositiveTimeH2Bound

M13/M17; WRAPPED integration support.

`intervalIntegral.integral_add_adjacent_intervals`, `intervalIntegral.integral_congr` and the FTC support the passage from E08 to an integrated H2 bound. The required H2/Laplacian/gradient identity is the native Fourier identity, not an independent Mathlib NSE lemma.

Replay the existing proof with frontier accumulation constant L_F. Its bound 3*L_F*(T-tau)+L_F/nu remains an actual derived budget.

## E10 / R7 -- frontierPositiveTimeAllOrders

M10/M13/M17; WRAPPED. M07 only under its exact additional hypotheses.

Minimum selection, translated intervals and integration support the induction. Reuse `GALERKIN_POSITIVE_TIME_ALL_ORDERS` with E09's seed; the actual high-order NSE differential estimate stays a Methlib dependency.

These are positive-time bounds on [tau,T], tau>0. No smoothness of the rough initial datum at t=0 is inferred.

## E11 / R8 -- frontierLimitNegativeHalf

M08/M09/M16/M02, with M12 as support S02; WRAPPED.

`MeasureTheory.lintegral_liminf_le'` passes uniform nonnegative square budgets to the modal limit. `MeasureTheory.integrable_norm_rpow_iff` converts the resulting finite square integral and measurability to MemLp. `MeasureTheory.Integrable.congr` transfers between equal-a.e. representatives.

Dominated convergence is usable for cutoff tails only when a genuine common integrable majorant is supplied. A weak/modal limit does not provide that majorant automatically. The actual derivative identification remains `criticalGalerkinLimit_rhs_memLp` and the physical Fourier bridge.

## E12 / R9 -- frontierLimitSharpQuartic

M08/M03/M16; WRAPPED.

`MeasureTheory.lintegral_liminf_le'`, `lintegral_const_mul''` and `lintegral_add_left'` support the nonnegative Fatou passage. Use the existing `critical_modal_quartic_budget` to retain the terminal-energy term jointly with the time integral.

The same subsequence and same critical limit must be used as in E11/E13. Separate existential solutions cannot be merged merely because their scalar estimates match.

## E13 -- FRONTIER_H12_NATIVE

M01/M08/M12/M16/M17; WRAPPED physical-assembly support.

`BoundedContinuousFunction.arzela_ascoli` requires a compact time domain, a common compact range and equicontinuity. Apply it to the native coefficient/compact-embedding construction, not to an arbitrary bounded ball in an infinite-dimensional Hilbert space. Prefer `CRITICAL_GALERKIN_GLOBAL_COMPACTNESS_WITH_STRONG_TRACE`.

`MeasureTheory.lintegral_iSup_directed` supports global-time exhaustion. `MeasureTheory.integrable_norm_rpow_iff` with p=4 supports the Serrin norm membership after the actual quartic estimate. `UnitAddTorus.hasSum_mFourier_series_L2` supports the physical carrier identification already organized by Methlib.

Neither compactness, Gronwall nor Lp membership alone supplies the physical NSE, pressure, strong initial trace, all-order smoothing or Leray-Hopf uniqueness. Reuse the already constructed native kernels with one common solution and frontier budgets.

## E14 -- FRONTIER_H12

M03 and E01/E02; DIRECT algebraic corollary support.

Convert the registered literature-normalized strict smallness condition to the exact native E13 hypothesis. Apply E13 without changing the datum, viscosity or physical conclusion. Mathlib square-root identities provide algebra, not a replacement for the quantitative norm bridge.

## Quantitative and logical safeguards

1. The pinned source is authoritative. Do not substitute current documentation identifiers or changed signatures without checking the pin.
2. Periodic fields do not satisfy Euclidean compact-support hypotheses merely because a torus is compact. A proved transfer is required.
3. Scalar, vector, tensor and derivative operator norms require explicit comparisons. No component factor may be silently removed.
4. Constant-coefficient Gronwall is not a theorem with arbitrary integrable time-dependent coefficient.
5. `MemLp.mono_exponent` assumes finite measure in the inspected source. It may be used on finite horizons, not automatically on (0,infinity).
6. Fatou provides a lower-semicontinuity inequality, not strong convergence. Dominated convergence requires domination.
7. Arzela-Ascoli needs compact range; boundedness of an infinite-dimensional norm ball is insufficient.
8. Generic conditions must be discharged by the actual NSE construction. A conditional wrapper does not earn `!=!` for a concrete frontier milestone.

## Implementation consequence

The library pass supplies reusable lower-level support for all fourteen milestones and a quantitative Sobolev/interpolation candidate for E03. It does not complete E03, identify K2, or compare C_F with C_repo. E15 remains independent.

Recommended implementation order remains S00 -> E01 -> E02 -> E03 -> the nine replay endpoints -> one-solution physical closure -> E14. Import pinned Mathlib modules; do not vendor library sources or reprove existing native wrappers. No Mathlib version, Lean source, runner or cache policy is changed by this indexing pass.
