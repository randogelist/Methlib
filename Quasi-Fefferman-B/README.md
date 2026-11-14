# Quasi-Fefferman-B: R10 cached assembly

```text
TARGET = QuasiFeffermanB.Endpoints.Root
EXACT_ROOT = QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
NATIVE_CI = Ubuntu 24.04 / Lean 4.33.0
SCHEDULER = independent dependency frontiers / 2 processes
NATIVE_ASYNC = Elab.async true
CACHE = exact source + transitive imports + compiler + dependency pins + object digest
AUDIT = fresh exact type and axiom report for every selected declaration
RESOLUTION_MARKER = !=! only after matching external compilation and axiom audit
ALLOWED_AXIOMS = {propext, Classical.choice, Quot.sound}
LOCAL_LEAN_EXECUTIONS = 0
ROOT_STATUS = A_TIER_CANDIDATE pending matching external evidence
FROZEN_CUTOFF = norm(a)^4 / (8*pi^2*nu^5)
```

The root and its 74-module import closure are assembled by the existing
external CI workflow. All 409 registered declarations receive fresh audits.
Parallel scheduling changes only independent process order; each dependency
frontier completes before dependent modules are submitted. Verified cached
objects retain their original producer identity and are audited again.

# Quasi-Fefferman-B: R8 source preload

| Current field | Value |
|---|---|
| Source preload | [SourcePreload/R8](SourcePreload/R8/README.md) |
| Pinned primary-source snapshots | `35` Lean files + `1` Mathlib license |
| Candidate proof-source normalizations | `7` modules; public statements unchanged |
| Selected QFB exports | `10`; [endpoint-index.json](QuasiFeffermanB/Endpoints/endpoint-index.json) |
| Mathematical continuation | Four R7 contracts and four complete derivation components |
| Latest cached run | [43523716429](https://github.com/randogelist/Methlib/actions/runs/43523716429) |
| Cached exact result | `42 PASS`; `7 FAIL`; `25 BLOCKED`; `227` audited declarations |
| Preserved cached identities | `42` dependency fingerprints; `227` declaration source hashes |
| R8 local Lean / new external runs | `0 / 0` |
| R8 source / root status | `A_TIER_CANDIDATE` |
| Frozen cutoff | `norm(a)^4 / (8*pi^2*nu^5)` |

```lean
import QuasiFeffermanB.Endpoints.Root
```

`EXTERNAL_CACHED_RUNNER = preload.cmd`  
`MATHEMATICAL_DERIVATION = B_TIER`  
`NEW_SOURCE_PROMOTION = PENDING_MATCHING_EXTERNAL_COMPILER_AND_THEOREM_AXIOM_AUDIT`

## Historical R6 package record

| Field | Value |
|---|---|
| Mode | `B_TIER_DERIVATION` |
| Continuation | `R6` endpoint preload; `R5` mathematical/source assembly |
| Exact root type | `QuasiFeffermanB.QuasiFeffermanBStatement` |
| Prepared root declaration | `QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED` |
| Mathematical / source status | `!=B_TIER`; `A_TIER_CANDIDATE` |
| Branch | `QUASI-FEFFERMAN-B` |
| Repository directory | `/Quasi-Fefferman-B/` |
| Formal root status | `PENDING_EXTERNAL_COMPILER_AND_THEOREM_AXIOM_AUDIT` |
| Implementation | Nine extracted endpoint modules; R5 support-interface repairs |
| Endpoint resolution marker | `!!` only after matching external compiler and axiom audit |
| Local Lean executions | `0` |

[QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt](QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt)

## R6 endpoint preload

```lean
import QuasiFeffermanB.Endpoints.Root
```

| Preload field | Exact value |
|---|---|
| Source probe | [preload.lean](preload.lean): ten selected exports, exact type/axiom commands |
| External Windows entry | [preload.cmd](preload.cmd), Lean `4.33.0` |
| Execution scope | Root plus its complete import closure: 74 modules, 71 audit modules, 409 declarations |
| Snapshot validation | All 79 source modules; exact committed source hashes |
| Immutable preload plan | [preload-plan.json](QuasiFeffermanB/Endpoints/preload-plan.json) |
| Cached baseline compatibility | 34 dependency fingerprints; 178 exact declaration source hashes |
| Cache reuse condition | Native pins, compiler version, transitive fingerprint and object SHA256 |
| Fresh audit requirement | Every registered declaration in the selected closure, including reused objects |
| Theorem/premise changes | `0` |
| Root promotion | Matching external compiler and root axiom audit required |

`run.cmd` without arguments retains the full-package audit. The cached CI
workflow and `preload.cmd` select `QuasiFeffermanB.Endpoints.Root`.
Target-scope success does not assert success for the five excluded modules.
The R5 counts and historical evidence below precede the R6 external preload.

## Current endpoint composition

[Extracted endpoint folder](QuasiFeffermanB/Endpoints/README.md)
contains the eight selected Q01 endpoints, the explicit caloric budget and
the deterministic root composition. The root consumes the original physical
Leray–Hopf existence statement and the existing exact admission chain.

R5 supplies candidate repairs for the six inherited failed modules and
applies the three previously derived import reductions. Source signatures,
analytic premises and the frozen cutoff are retained. Recursive source
fingerprinting and audit registration now include the endpoint subfolder.

Evidence baseline: [run 43151440082](https://github.com/randogelist/Methlib/actions/runs/43151440082),
commit `e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c`.
The baseline contains 178 exact audited declarations. R5 introduces no
new external compiler evidence and no new A-tier promotion.

The status and declaration tables below retain the historical initial
assembly and its earlier audit provenance.

## External endpoint status

`LOCAL_LEAN_EXECUTIONS = 0`.

`!!` = the exact named endpoint passed the external compiler and its
matching theorem-level axiom audit; permitted axioms:
`propext`, `Classical.choice`, `Quot.sound`.

`endpoint-manifest.json` pins candidate source hashes and audited names.
The external evidence artifact records compiler-emitted types and axiom lists.
Passing intermediate implications retain every displayed premise; they do
not automatically resolve the larger Q/A endpoint.

| Endpoints | Initial implementation status |
|---|---|
| Q00 | Concrete physical carrier and exact root contract defined |
| Q01 | Energy-level Fourier compactness candidates; actual LH limit pending |
| Q02 | Native LH energy theorem candidate |
| Q03–Q04 | `!!` Exact physical interpolation and native LH budget |
| Q05 | Native full LH restart candidate |
| Q06 | Exact numerical caloric admission pending |
| Q07 | Native strict good-time theorem candidate |
| Q08–Q10 | Actual comparison, smoothing, and pressure adapters in progress |
| Q11–Q12 | Tail energy and unique future assembly pending |
| Q13 | Scalar cutoff and zero-LH smooth-representative candidates |
| Q14 | Concrete root contract fixed; root proof pending |
| A01–A11 | Independent caloric lemmas in progress; full admission pending |

[External compiler workflow](../.github/workflows/quasi-fefferman-b.yml)
· [Candidate manifest](endpoint-manifest.json)
· [Native Windows runner](run.cmd)

## Historical verified exact declarations

`!!` = exact external compiler and standard-only theorem axiom audit.

Evidence: [run 43150307199](https://github.com/randogelist/Methlib/actions/runs/43150307199),
commit `7da82ecbe5c90a68bb85781190acbeca4e2d2489`.

[Source, dependency and axiom ledger](evidence/run-43150307199-reinspection.json).
Exact passes: **120 declarations, 20 modules**. Each theorem retains all
premises in its pinned source. No module-name or declaration-count heuristic
establishes the unconditional root.

| Frozen endpoint | Status | Exact evidence |
|---|---|---|
| Q03 Fourier Hhalf interpolation | `!!` | `physicalH1_halfEnergy_midpoint`; literal extended Fourier energy |
| Q04 native LH fourth-power budget | `!!` | `LH_HALF_ENERGY_AE_FINITE`, `LH_HALF_ENERGY_AEMEASURABLE`, `LH_FOURTH_POWER_BUDGET` |
| A01 symmetric Euclidean Leray multiplier | `!!` | `SYMMETRIC_COMPLEX_LERAY_MULTIPLIER`, scaled variant |
| A05 continuous quadratic barrier | `!!` | `CONTINUOUS_QUADRATIC_BARRIER` and its square-budget consequences |
| Q02 zero-inclusive energy endpoint | `PENDING` | Positive-horizon `LH_ENERGY_BOUNDS` verified; zero-inclusive wrapper prepared |
| Q01 arbitrary-L2 LH existence | `PENDING` | Physical weak momentum and interval energy passage under construction |
| Q06 exact H1 admission | `PENDING` | Full numerical candidate chain prepared; external compiler pending |
| Remaining Q/A endpoints and canonical root | `PENDING` | No promotion from prepared code |

| Marker | Exact declaration |
|---|---|
| `!!` | `QuasiFeffermanB.CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION` |
| `!!` | `QuasiFeffermanB.CALORIC_H1_GALERKIN_H2_BUDGET` |
| `!!` | `QuasiFeffermanB.CALORIC_H1_POSITIVE_FLOW_OF_GALERKIN_LIMIT` |
| `!!` | `QuasiFeffermanB.CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE` |
| `!!` | `QuasiFeffermanB.CONTINUOUS_QUADRATIC_BARRIER` |
| `!!` | `QuasiFeffermanB.CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY` |
| `!!` | `QuasiFeffermanB.CUTOFF_NONNEG` |
| `!!` | `QuasiFeffermanB.CUTOFF_POS` |
| `!!` | `QuasiFeffermanB.CUTOFF_ZERO` |
| `!!` | `QuasiFeffermanB.ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE` |
| `!!` | `QuasiFeffermanB.ENERGY_GALERKIN_GLOBAL_COEFFICIENT_SUBSEQUENCE` |
| `!!` | `QuasiFeffermanB.ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM` |
| `!!` | `QuasiFeffermanB.ENERGY_SLICE_CUTOFF` |
| `!!` | `QuasiFeffermanB.FINITE_CONVECTION_ENERGY_LE_CHI0` |
| `!!` | `QuasiFeffermanB.FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0` |
| `!!` | `QuasiFeffermanB.FINITE_SYNTHESIS_NORM_LE_CHI0` |
| `!!` | `QuasiFeffermanB.GALERKIN_CHI0_CONTINUOUS` |
| `!!` | `QuasiFeffermanB.GALERKIN_CRITICAL_COMPACTNESS_OF_ENSTROPHY` |
| `!!` | `QuasiFeffermanB.GALERKIN_CRITICAL_RHS_SQUARE_OF_ENSTROPHY_BOUND` |
| `!!` | `QuasiFeffermanB.GALERKIN_ENSTROPHY_ACCUMULATION_OF_CONTROL` |
| `!!` | `QuasiFeffermanB.GALERKIN_ENSTROPHY_RATE_OF_TRANSPORT_SQUARE` |
| `!!` | `QuasiFeffermanB.GALERKIN_H1_INITIAL_ENSTROPHY_BOUND` |
| `!!` | `QuasiFeffermanB.GALERKIN_H2_SEED_OF_ENSTROPHY_ACCUMULATION` |
| `!!` | `QuasiFeffermanB.GALERKIN_POSITIVE_FLOW_OF_H2_SEED` |
| `!!` | `QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW` |
| `!!` | `QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE` |
| `!!` | `QuasiFeffermanB.LH_CONSTANT_PAIRING_PRESERVED` |
| `!!` | `QuasiFeffermanB.LH_ENERGY_BOUNDS` |
| `!!` | `QuasiFeffermanB.LH_FOURTH_POWER_BUDGET` |
| `!!` | `QuasiFeffermanB.LH_HALF_ENERGY_AEMEASURABLE` |
| `!!` | `QuasiFeffermanB.LH_HALF_ENERGY_AE_FINITE` |
| `!!` | `QuasiFeffermanB.LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO` |
| `!!` | `QuasiFeffermanB.PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT` |
| `!!` | `QuasiFeffermanB.POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN` |
| `!!` | `QuasiFeffermanB.QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET` |
| `!!` | `QuasiFeffermanB.QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET` |
| `!!` | `QuasiFeffermanB.QUADRATIC_BARRIER_SQUARE_BUDGET` |
| `!!` | `QuasiFeffermanB.QUADRATIC_BARRIER_ZERO_HEAT_BUDGET` |
| `!!` | `QuasiFeffermanB.SAFE_CUTOFF_GT` |
| `!!` | `QuasiFeffermanB.STRICT_CALORIC_DISCRIMINANT` |
| `!!` | `QuasiFeffermanB.STRICT_CALORIC_QUADRATIC_BUDGET` |
| `!!` | `QuasiFeffermanB.SYMMETRIC_COMPLEX_LERAY_MULTIPLIER` |
| `!!` | `QuasiFeffermanB.SYMMETRIC_COMPLEX_LERAY_MULTIPLIER_SCALED` |
| `!!` | `QuasiFeffermanB.SYMMETRIC_SPLIT_SCALAR_SQUARE` |
| `!!` | `QuasiFeffermanB.TWO_LH_EQUAL_OF_POSITIVE_FLOW_TRACE_AND_SERRIN` |
| `!!` | `QuasiFeffermanB.caloricBilinearConstant_pos` |
| `!!` | `QuasiFeffermanB.caloricBilinearConstant_sq` |
| `!!` | `QuasiFeffermanB.caloricHeatBudget_nonneg` |
| `!!` | `QuasiFeffermanB.caloricHeatBudget_sq` |
| `!!` | `QuasiFeffermanB.caloric_criticalEnergy_four_eq_laplacian` |
| `!!` | `QuasiFeffermanB.caloric_criticalEnergy_le_succ` |
| `!!` | `QuasiFeffermanB.caloric_criticalEnergy_one_le_enstrophy` |
| `!!` | `QuasiFeffermanB.caloric_criticalEnergy_three_le_laplacian` |
| `!!` | `QuasiFeffermanB.caloric_fourierCharacter_norm` |
| `!!` | `QuasiFeffermanB.coefficientLeray_transport_symmetric` |
| `!!` | `QuasiFeffermanB.coefficientTransport_frequencyDot` |
| `!!` | `QuasiFeffermanB.coefficientTransport_symmetric` |
| `!!` | `QuasiFeffermanB.complexTransverse_pythagoras` |
| `!!` | `QuasiFeffermanB.complexTransverse_symmetric` |
| `!!` | `QuasiFeffermanB.complexVecNorm_add_le` |
| `!!` | `QuasiFeffermanB.complexVecNorm_eq_norm` |
| `!!` | `QuasiFeffermanB.complexVecNorm_finset_sum_le` |
| `!!` | `QuasiFeffermanB.complexVecNorm_nonneg` |
| `!!` | `QuasiFeffermanB.complexVecNorm_smul` |
| `!!` | `QuasiFeffermanB.complexVecNorm_sq` |
| `!!` | `QuasiFeffermanB.constant_positive_solenoidal_test` |
| `!!` | `QuasiFeffermanB.constant_weak_momentum_integrand` |
| `!!` | `QuasiFeffermanB.criticalEnergy_midpoint` |
| `!!` | `QuasiFeffermanB.criticalFourthPower_budget` |
| `!!` | `QuasiFeffermanB.criticalFourthPower_integrable` |
| `!!` | `QuasiFeffermanB.datumFourierCoeff_tendsto_of_L2` |
| `!!` | `QuasiFeffermanB.energyCutoff_nonneg` |
| `!!` | `QuasiFeffermanB.energyGalerkin_H0_time_difference_bound` |
| `!!` | `QuasiFeffermanB.energyModeRhsBound_nonneg` |
| `!!` | `QuasiFeffermanB.energyModeTransportBound_nonneg` |
| `!!` | `QuasiFeffermanB.energyModeTransport_norm_le` |
| `!!` | `QuasiFeffermanB.energyTimeH0L2_norm_sq` |
| `!!` | `QuasiFeffermanB.energyTimeH0L2_sub_norm_sq` |
| `!!` | `QuasiFeffermanB.energy_H0_tail_sq` |
| `!!` | `QuasiFeffermanB.energy_coefficient_curve_precompact` |
| `!!` | `QuasiFeffermanB.finiteChi0_nonneg` |
| `!!` | `QuasiFeffermanB.finite_convolution_swap` |
| `!!` | `QuasiFeffermanB.fullFourierRhs_energy_bound` |
| `!!` | `QuasiFeffermanB.galerkin_H0_energy_bound` |
| `!!` | `QuasiFeffermanB.galerkin_H0_norm_sq` |
| `!!` | `QuasiFeffermanB.galerkin_energy_coefficient_modulus` |
| `!!` | `QuasiFeffermanB.globalEnergyCoefficient_continuousOn` |
| `!!` | `QuasiFeffermanB.globalEnergyCoefficient_eq_horizon` |
| `!!` | `QuasiFeffermanB.globalEnergyCoefficient_uniform_limit` |
| `!!` | `QuasiFeffermanB.norm_component_le_complexVecNorm` |
| `!!` | `QuasiFeffermanB.physicalEnergy_compCLM_tendsto_of_L2` |
| `!!` | `QuasiFeffermanB.physicalEnergy_eq_toLp_norm_sq` |
| `!!` | `QuasiFeffermanB.physicalEnergy_tendsto_of_L2` |
| `!!` | `QuasiFeffermanB.physicalH1HalfDatum_norm_sq` |
| `!!` | `QuasiFeffermanB.physicalH1_cutoff_bounds` |
| `!!` | `QuasiFeffermanB.physicalH1_cutoff_midpoint` |
| `!!` | `QuasiFeffermanB.physicalH1_halfEnergy_le` |
| `!!` | `QuasiFeffermanB.physicalH1_halfEnergy_midpoint` |
| `!!` | `QuasiFeffermanB.physicalH1_halfEnergy_ne_top` |
| `!!` | `QuasiFeffermanB.physicalH1_halfEnergy_summable` |
| `!!` | `QuasiFeffermanB.physicalH1_mem_halfSobolev` |
| `!!` | `QuasiFeffermanB.physicalHalfEnergyTerm_nonneg` |
| `!!` | `QuasiFeffermanB.physicalHalfEnergyTerm_of_meanZero` |
| `!!` | `QuasiFeffermanB.physicalHalfEnergy_aemeasurable` |
| `!!` | `QuasiFeffermanB.physicalHalfEnergy_cutoff` |
| `!!` | `QuasiFeffermanB.physicalHalfEnergy_toReal_eq_tsum` |
| `!!` | `QuasiFeffermanB.physical_inner_congr_left_ae` |
| `!!` | `QuasiFeffermanB.positive_timeDerivative_translate` |
| `!!` | `QuasiFeffermanB.restartTest_eq` |
| `!!` | `QuasiFeffermanB.restartTest_is_test` |
| `!!` | `QuasiFeffermanB.restartTest_timeDerivative` |
| `!!` | `QuasiFeffermanB.restartTimeClamp_contDiff` |
| `!!` | `QuasiFeffermanB.restartTimeClamp_eq` |
| `!!` | `QuasiFeffermanB.restartTimeClamp_hasDerivAt` |
| `!!` | `QuasiFeffermanB.restartTimeClamp_pos` |
| `!!` | `QuasiFeffermanB.timeTranslate_ae_Ioc` |
| `!!` | `QuasiFeffermanB.timeTranslate_integrated_momentum` |
| `!!` | `QuasiFeffermanB.timeTranslate_measurePreserving_Ioc` |
| `!!` | `QuasiFeffermanB.timeTranslate_memLp_Ioc` |
| `!!` | `SingularClosure.GalerkinSolution.energy_H0_time_tail` |

`QFB_ROOT_UNCONDITIONAL_A_TIER = PENDING`.

## Frozen statement

$$
\mathbb T^3=(\mathbb R/\mathbb Z)^3,\qquad \nu>0,\qquad f=0,
\qquad E=L^2_{\sigma,0}(\mathbb T^3;\mathbb R^3).
$$

$$
T_*(a,\nu)=\frac{\|a\|_2^4}{8\pi^2\nu^5}.
$$

$$
\forall a\in E:\quad \mathrm{LH}_\nu(a)\ne\varnothing,
\qquad
\forall u\in\mathrm{LH}_\nu(a),\ \forall\delta>T_*(a,\nu):
\quad (u,p)\in C^\infty([\delta,\infty)\times\mathbb T^3).
$$

$$
\forall t\ge\delta:\quad
\|u(t)\|_2^2+2\nu\int_\delta^t\|\nabla u(s)\|_2^2\,ds
=\|u(\delta)\|_2^2,
\qquad
\mathrm{LH}_\nu(u(\delta))=\{r\mapsto u(\delta+r)\}.
$$

`sigma` = distributional divergence zero; `0` = spatial mean zero.
`LH` = standard Leray–Hopf trajectories, including strong initial trace.
Smoothness = existence of smooth representatives; pressure = zero-mean gauge.
Velocity equality = equality of the weakly continuous L² trajectories.
Initial-history uniqueness and arbitrary positive cutoffs are outside scope.

## Concrete implication chain

$
M:=\|a\|_2,\qquad
L(v):=\|v\|_2^2,\qquad
D(v):=\|\nabla v\|_2^2,\qquad
H(v):=\sum_{k\ne0}2\pi|k|\,|\widehat v(k)|^2.
$

$
H(v)=\|v\|_{\dot H^{1/2}}^2
\quad(v\in H^{1/2}_{\sigma,0}),\qquad
H:L^2_{\sigma,0}\longrightarrow[0,\infty].
$

### Q00–Q02: actual existence and energy

$
a\in E
\Longrightarrow
\mathrm{LH}_\nu(a)\ne\varnothing.
$

$
\forall u\in\mathrm{LH}_\nu(a),\ \forall\delta>0,\ \forall t\ge0:
\quad
L(u(t))\le M^2,\qquad
\int_0^\delta D(u(t))\,dt\le\frac{M^2}{2\nu}.
$

### Q03–Q04: Fourier interpolation and time budget

$
\begin{aligned}
H(v)
&=\sum_{k\ne0}|\widehat v(k)|\,
                 \bigl(2\pi|k|\,|\widehat v(k)|\bigr)\\
&\le
\left(\sum_{k\ne0}|\widehat v(k)|^2\right)^{1/2}
\left(\sum_{k\ne0}4\pi^2|k|^2|\widehat v(k)|^2\right)^{1/2}.
\end{aligned}
$

$
v\in H^1_{\sigma,0}
\Longrightarrow
H(v)^2\le L(v)D(v).
$

$
\boxed{
\int_0^\delta H(u(t))^2\,dt
\le M^2\int_0^\delta D(u(t))\,dt
\le\frac{M^4}{2\nu}.}
$

Measurability: nonnegative finite Fourier sums → monotone extended sum.

### Q05: admissible restart times

$
\exists R_u\subset(0,\infty):
\quad |(0,\infty)\setminus R_u|=0,
$

$
s\in R_u
\Longrightarrow
\begin{cases}
u(s)\in H^1_{\sigma,0},\\
\operatorname{Shift}_s u\in\mathrm{LH}_\nu(u(s)),\\
\displaystyle\lim_{r\downarrow0}
\|u(s+r)-u(s)\|_2=0.
\end{cases}
$

$
(\operatorname{Shift}_s u)(r):=u(s+r).
$

Construction: countable intersection of compatible energy-start sets and
H¹-trace sets; weak continuity + the energy inequality at s → strong right trace.

### Q07: strict good-time selection

$
\delta>T_*(a,\nu)=\frac{M^4}{8\pi^2\nu^5}
\Longrightarrow
\exists s\in R_u\cap(0,\delta):
H(u(s))<2\pi\nu^2.
$

Integral contradiction:

$
H(u(t))\ge2\pi\nu^2\ \text{a.e. on }(0,\delta)
\Longrightarrow
4\pi^2\nu^4\delta
\le\int_0^\delta H(u(t))^2\,dt
\le\frac{M^4}{2\nu},
$

$
\Longrightarrow\quad
\delta\le T_*(a,\nu)\quad\bot.
$

### Q06, A01–A11: exact admission of the selected trace

$
b:=u(s),\qquad
Q(b):=
\left[
\int_0^\infty
\left(\sum_{k\ne0}|\widehat b(k)|e^{-4\pi^2|k|^2t}\right)^2dt
\right]^{1/2}.
$

$
\boxed{
H(b)<2\pi\nu^2
\Longrightarrow
Q(b)^2\le\frac{H(b)}{4\pi}<\frac{\nu^2}{2}
\Longrightarrow
Q(b)<\frac{\nu}{\sqrt2}
\Longrightarrow
\operatorname{Reg}_\nu(b).}
$

$
\operatorname{Reg}_\nu(b):=
\exists(v,p_b):
\quad
\mathrm{LH}_\nu(b)=\{v\},\quad
\lim_{t\downarrow0}\|v(t)-b\|_2=0,\quad
(v,p_b)\in C^\infty((0,\infty)\times\mathbb T^3),
$

with the LH energy equality and zero-mean pressure gauge.

Schur subchain:

$
\Theta(t):=\sum_{k\in\mathbb Z^3}e^{-t|k|^2},\qquad
\Theta(t)-1\le(\pi/t)^{3/2}
$

$
\Longrightarrow\
\sum_{\ell\ne0}
\frac1{|\ell|^2(r^2+|\ell|^2)}
\le\frac{2\pi^2}{r}
\Longrightarrow\
Q(b)^2\le\frac{H(b)}{4\pi}.
$

Caloric subchain:

$
\chi_0(v):=\sum_{k\ne0}|\widehat v(k)|,\qquad
Y:=L^2((0,\infty);\ell^1),\qquad
\beta_\nu:=\frac1{2\sqrt{2\nu}},\qquad
h:=\frac{Q(b)}{\sqrt\nu}.
$

$
B_\nu(v,w)(t):=
-\frac12\int_0^t e^{\nu(t-r)\Delta}
\mathbb P\nabla\!\cdot(v\otimes w+w\otimes v)(r)\,dr.
$

$
\|B_\nu(v,w)\|_Y\le\beta_\nu\|v\|_Y\|w\|_Y,\qquad
\|e^{\nu t\Delta}b\|_Y=h.
$

$
Q(b)<\frac{\nu}{\sqrt2}
\Longrightarrow
4\beta_\nu h<1
\Longrightarrow
\sup_N\int_0^\infty\chi_0(u_N(t))^2\,dt
\le S:=\frac{4Q(b)^2}{\nu}.
$

$
\frac{d}{dt}\|\nabla u_N\|_2^2+\nu\|\Delta u_N\|_2^2
\le\nu^{-1}\chi_0(u_N)^2\|\nabla u_N\|_2^2
$

$
\Longrightarrow\
\|\nabla u_N(t)\|_2^2
\le\frac{\|b\|_2^2e^{S/\nu}}{2\nu t}
\Longrightarrow\
\operatorname{Reg}_\nu(b).
$

Final analytic composition:
Galerkin compactness + retained caloric budget + positive-time H¹/H²
bounds + parabolic smoothing + all-LH relative-energy comparison.

### Q08–Q10: identification of the original trajectory

$
\mathrm{LH}_\nu(b)=\{v\},\qquad
\operatorname{Shift}_s u\in\mathrm{LH}_\nu(b)
\Longrightarrow
\operatorname{Shift}_s u=v.
$

$
s<\delta,\quad
(v,p_b)\in C^\infty((0,\infty)\times\mathbb T^3)
\Longrightarrow
\boxed{(u,p)\in C^\infty([\delta,\infty)\times\mathbb T^3).}
$

$
-\Delta p=\sum_{i,j}\partial_i\partial_j(u_i u_j),\qquad
\int_{\mathbb T^3}p(t,x)\,dx=0.
$

### Q11–Q14: energy, trace uniqueness, and root

$
\forall t\ge\delta:
\quad
L(u(t))+2\nu\int_\delta^tD(u(r))\,dr=L(u(\delta)).
$

$
\mathrm{LH}_\nu(u(\delta))
=\{\operatorname{Shift}_\delta u\}.
$

$
a\ne0\Longrightarrow2T_*(a,\nu)>T_*(a,\nu),\qquad
a=0\Longrightarrow(u,p)=(0,0).
$

$
\boxed{
\mathrm{Q01}+\mathrm{Q09}+\mathrm{Q10}+
\mathrm{Q11}+\mathrm{Q12}+\mathrm{Q13}
\Longrightarrow
\mathrm{Q14}=\texttt{Quasi\_Fefferman\_B}.}
$

Full derivations and exact endpoint signatures:
[TXT §§2–3, §6, Appendix A](QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt).

## Reuse baseline

| Object | Pinned evidence |
|---|---|
| Source revision | `09dfe94a1ef150e21d09df3013fbe09002ef139c` |
| Imported foundation | `regularity-B-assembly/Singular-Axiomatic-closure` |
| Compiler | external Lean `4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Base audit | 204 matching exact-type/axiom reports |
| Branch/tree inventory | 28 repositories; 172 pre-existing branch tips |

[Pinned foundation](https://github.com/randogelist/Methlib/tree/09dfe94a1ef150e21d09df3013fbe09002ef139c/regularity-B-assembly/Singular-Axiomatic-closure)
· [Cached external evidence](https://github.com/randogelist/Methlib/actions/runs/43059293572)

Existing verified admission:

$$
C_{\mathrm{NL}}\|b\|_{\dot H^{1/2}}<\nu
\Longrightarrow \operatorname{Reg}_\nu(b).
$$

Required numerical admission:

$$
\|b\|_{\dot H^{1/2}}^2<2\pi\nu^2
\Longrightarrow \operatorname{Reg}_\nu(b).
$$

`C_NL` has no verified numerical upper bound in the selected foundation.
The second implication remains a new formal endpoint; its mathematical
caloric/theta–Schur derivation is included in the TXT.

## Concrete reuse map

Base namespace: SingularClosure.
Evidence scope: exact existing declaration types at the pinned source;
new adapters and new root remain uncompiled.

| Existing endpoint | Concrete role | Remaining formal obligation |
|---|---|---|
| CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE; GALERKIN_ENERGY_IDENTITY | Q01 approximants and A06 finite energy | Arbitrary-L² infinite-dimensional LH limit |
| FINITE_PHYSICAL_ENERGY_PARSEVAL; FINITE_PHYSICAL_ENSTROPHY_PARSEVAL | Q03 Fourier/physical normalization | Infinite H¹ midpoint interpolation |
| CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON | Q08/Q12 relative-energy comparison | Compatible regular reference and translated LH semantics |
| INFINITE_TRANSPORT_PRESSURE_RECOVERY; SOBOLEV_TRANSPORT_PRESSURE_JOINT_SMOOTH | Q10 pressure recovery | Compatible positive-time Sobolev flow |
| NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL | Verified C-small actual-PDE baseline | Exact numerical admission Q06 |
| NSE.squaredNormInterpolation; NSE.fourthPowerIntegrable; NSE.integratedSerrinBound (stokes-conditional) | Q04 scalar integral algebra | Actual measurable Fourier profile and physical interpolation |

Reuse source/evidence URLs and exact premises: TXT Appendices B–E.
An existing theorem's hypotheses remain required after import.
The standard-only axiom audit does not discharge a quantified analytic premise.

## Endpoint plan

| Endpoints | Contract |
|---|---|
| Q00–Q03 | Physical semantics; arbitrary-L² LH existence; energy; midpoint interpolation |
| Q04–Q05 | Measurable critical-time budget; conull restart with strong right trace |
| Q06; A01–A11 | Exact numerical admission through caloric and theta–Schur estimates |
| Q07–Q10 | Strict good-time selection; same-trajectory identification; smooth tail and pressure |
| Q11–Q14 | Energy equality; trace uniqueness; zero case; deterministic root assembly |

`ROOT_A_TIER = PENDING_EXTERNAL_COMPILER_AND_THEOREM_AXIOM_AUDIT`.

Subsequent formalization: pinned-cache reuse; independent endpoint bodies;
native asynchronous elaboration where dependency-safe; deterministic root.
All source, semantic, analytic, admission, and audit obligations remain
explicit until discharged. No local Lean execution.

