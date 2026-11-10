# Lean Scout: Ten \(H^{1/2}\) Representation Classes

```text
HANDOUT_DATE=2026-11-10
SCOPE=PERIODIC_CRITICAL_H12_REPRESENTATIONS
LOCAL_LEAN_EXECUTION=NONE
ROOT_REPOSITORY=randogelist/Methlib
ROOT_DIRECTORY=regularity-B-assembly
```

## Evidence levels

| Code | Meaning |
|---|---|
| `A_M` | Methlib declaration with recorded matching external native PASS and theorem-level axiom status. |
| `A_H@c6b95` | HVR declaration contained in the audited checkpoint at commit `c6b95fd9e3d792270026da083bddddbc72bacb22`. |
| `S` | Lean source exists, but no matching external compiler and theorem-level axiom-audit evidence was located. |
| `OPEN` | The exact representation core was not located. |

The HVR evidence is commit-scoped: Lean 4.33.0, 118 preserved Lean source
modules, 641 audited declarations, source-integrity verification, exact endpoint
type checks, and approved axioms restricted to
`propext`, `Classical.choice`, and `Quot.sound`. This does not establish H00
admissibility, a finite checker equivalence, or unconditional RH.

## Global scout result

| Class | Representation | Existing reusable layer | Exact missing core | Readiness |
|---:|---|---|---|---|
| T1 | Galerkin | finite Fourier, Leray, Parseval, finite Stokes identities | cutoff tower and reconstruction | strong partial |
| T2 | Stokes fractional domain | critical spectral energies and finite \(A^{1/4}\) dictionary | infinite operator-domain equivalence | strong partial |
| T3 | Poisson semigroup | abstract contractive-orbit machinery | actual \(e^{-aA^{1/2}}\) module | new analytic core |
| T4 | Heat semigroup | actual heat multiplier and \(H^{1/2}\) contraction | semigroup, generator, and trace completion | strongest direct core |
| T5 | GP–SOLOBOLO | GP/Widder/moment interfaces | actual Stokes spectral GP transform | strong abstract scaffold |
| T6 | BKQR | half-moment, spectral lift, defect square, Hardy transfer | actual \(\delta_h=(I-Q_h)/h\) realization | strongest cross-branch reuse |
| T7 | Cayley–Sturmion | moment codec and contractive Cayley geometry | Stokes Cayley operator and Chebyshev orbit | interface scaffold |
| T8 | Resolvent/HVR | audited scalar measure-resolvent calculus | vector Stokes resolvent | strong scalar scaffold |
| T9 | Physical realization | finite Parseval and finite Stokes-quarter realization | inverse infinite Fourier synthesis | strong partial |
| T10 | GP–Borel | Bochner and differentiation infrastructure | exact Borel orbit and two-parameter lift | new conditional core |

---

# T1. `H12_FINITE_GALERKIN_REPRESENTATION`

## Directly reusable declarations

Source: [`../pkg1/H12_FOURIER_FOUNDATIONS.lean`](../pkg1/H12_FOURIER_FOUNDATIONS.lean)

```lean
Mode3
freq
freq_nonneg
freq_zero
freq_neg
freq_add_le
solenoidalSubmodule
SolenoidalAt
leray
leray_solenoidal
leray_norm_le
rawTransportCoeff
projectedTransportCoeff
projectedTransport_solenoidal
projectedTransport_norm_le
```

Source: [`../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean`](../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean)

```lean
hhalfFinset
honeFinset
hthreeHalfFinset
honeTerm_sq_eq_hhalf_mul_hthreeHalf
finite_critical_interpolation
```

The finite interpolation endpoint is

\[
E_{1,N}(u)^2\le E_{1/2,N}(u)E_{3/2,N}(u).
\]

Sources:

- [`../pkg2/CEA07E_TorusParseval.lean`](../pkg2/CEA07E_TorusParseval.lean)
- [`../pkg2/CEA07F_TorusStokesQuarter.lean`](../pkg2/CEA07F_TorusStokesQuarter.lean)

Reusable physical declarations include

```lean
torus_scalar_finite_parseval
torus3_vector_finite_parseval
torus3_l2_dictionary_field
torus3_l2_spectral_eq_physical
```

## Missing exact core

```lean
galerkinCutoff : ℕ → Mode3 → Bool
galerkinProj : ℕ → H12Datum → H12Datum

galerkinProj_idempotent
galerkinProj_nested
galerkinProj_selfAdjoint
galerkinProj_hhalf_le
galerkinProj_hhalf_tendsto

CompatibleGalerkinTower
encodeGalerkinTower
decodeGalerkinTower
decode_encode_galerkin
encode_decode_galerkin
```

Principal unresolved limit:

\[
q(u-P_Nu)\longrightarrow0.
\]

```text
T1=A_M finite core + OPEN tower completion
```

---

# T2. `H12_STOKES_FRACTIONAL_DOMAIN_REPRESENTATION`

## Directly reusable declarations

From the critical spectral package:

```lean
hhalfSq
honeTerm
hhalfFinset
honeFinset
hthreeHalfFinset
finite_critical_interpolation
hhalfSq_nonneg
```

Source: [`../pkg2/CEA07D_StokesSpectralDictionary.lean`](../pkg2/CEA07D_StokesSpectralDictionary.lean)

```lean
criticalWeight
finite_stokes_criticalWeight_identity
FiniteStokesDictionary
finite_stokes_dictionary_identity
finite_bkqr_to_stokes_critical
```

Compiled finite identity:

\[
\sum_i\left(1+\sqrt{h\lambda_i}\right)e_i
=
\sum_i e_i+\sqrt h\sum_i\sqrt{\lambda_i}\,e_i.
\]

Source: [`../pkg2/CEA07F_TorusStokesQuarter.lean`](../pkg2/CEA07F_TorusStokesQuarter.lean)

```lean
torus3ModeSq
torus3StokesEigenvalue
torus3StokesEigenvalue_nonneg
torus3A14SpectralSq
torus3CriticalSpectralSq
torus3_criticalWeight_spectral_identity
torus3_stokes_quarter_dictionary
```

This identifies the finite Fourier weight

\[
\sqrt{\lambda_k}=2\pi|k|
\]

with the Stokes-quarter spectral energy.

## Missing exact core

No located theorem states an infinite-space equivalence

\[
H^{1/2}_{\sigma,0}=D(A^{1/4})
\]

as equality or linear isometry of actual Lean spaces.

```lean
stokesEigenvalue : Mode3 → ℝ
stokesPowMultiplier : ℝ → Mode3 → ℝ
StokesFractionalDomain : ℝ → Type

h12_iff_mem_stokesQuarterDomain
stokesQuarter_norm_sq_eq_hhalfSq
stokes_kernel_eq_constant_modes
stokes_meanZero_orthogonal_split
```

```text
T2=A_M finite spectral dictionary + OPEN infinite domain realization
```

---

# T3. `H12_POISSON_SEMIGROUP_REPRESENTATION`

## Reusable abstract layer

Pinned HVR sources:

- [`Frontier/ContractiveOrbitFrontier.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/Frontier/ContractiveOrbitFrontier.lean)
- [`Derivations/BKQR/DefectGramSquare.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/Derivations/BKQR/DefectGramSquare.lean)
- [`RH_HilbertLimit/TwoRoutes/RouteTwoContractive.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/RH_HilbertLimit/TwoRoutes/RouteTwoContractive.lean)

```lean
RealGramGeometry
orbitIter
BKQRContractiveOrbit
BKQRContractiveOrbitFrontier
ORBIT_DEPTH_ENERGY_LE_BASE
contractiveOrbit_abs_le_base
contractiveOrbit_absolute_summability
```

These apply after an actual realization

\[
T=Q_h=e^{-hA^{1/2}}
\]

has been supplied.

## Missing exact core

```lean
poissonFactor (a : ℝ) (k : Mode3) :=
  Real.exp (-a * freq k)

poissonCoeff
poissonDatum
poisson_zero
poisson_add
poisson_contracts_hhalf
poisson_tendsto_zero
poisson_deriv
poisson_iteratedDeriv
poisson_trace_identity
```

The abstract orbit layer does not establish the semigroup law, generator
identity, or critical trace formula.

```text
T3=A_H@c6b95 abstract scaffold + OPEN actual Poisson core
```

---

# T4. `H12_HEAT_SEMIGROUP_REPRESENTATION`

## Directly reusable actual core

Source: [`../pkg1/H12_FOURIER_FOUNDATIONS.lean`](../pkg1/H12_FOURIER_FOUNDATIONS.lean)

```lean
heatFactor
heatFactor_pos
heatFactor_le_one
heatCoeff
heatCoeff_zero_time
heatCoeff_solenoidal
hhalfTerm_heat_le
heatDatum
heatDatum_coeff
```

The multiplier is

\[
e^{-\nu(2\pi|k|)^2t}.
\]

Source: [`../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean`](../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean)

```lean
heat_hhalfSq_le
```

with

\[
q(e^{-\nu tA}u)\le q(u).
\]

## Missing completion

```lean
heatCoeff_add_time
heatDatum_add_time
heatDatum_tendsto_zero
heatCoeff_hasDerivAt
heat_generator_identity
heat_smoothing_bound
heat_critical_trace_identity
```

The five restriction instances should subsequently be thin wrappers over the
single carrier lattice.

```text
T4=A_M actual core; completion cost minimal
```

---

# T5. `H12_GP_SOLOBOLO_REPRESENTATION`

## Reusable GP/Widder interfaces

Pinned HVR sources:

- [`Core/Observable.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/Core/Observable.lean)
- [`Frontier/OurFrontier.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/Frontier/OurFrontier.lean)
- [`Frontier/FreeEnergyFrontier.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/Frontier/FreeEnergyFrontier.lean)

```lean
GPObservable
PositiveAnchor
InteriorRadius
CayleyMomentCodec
GPTransferMomentModel
GPCayleyTransferMatch
GPBKQRCommonMomentIdentity
logScaleCurvature
widderStep
widderTower
widderTower_zero
widderTower_succ
GPWidderGeneratedModel
GPWidderGeneratedModel.toTransferMomentModel
GPBKQRFreeEnergyCurvature
```

Available architecture:

\[
\text{base moment}
\longmapsto
\text{Widder tower}
\longmapsto
\text{decoded GP observable}.
\]

## Missing H12 instantiation

```lean
h12SpectralMeasure
h12GP
h12GP_nonneg
h12GP_at_zero_two
h12GP_derivative_ladder
h12GP_hankel_psd
h12GP_logConvex
h12VectorGPTower
h12VectorGPTower_recover
```

The existing `actualThetaCayleyObservable` is a \(\Theta'/\Theta\) pole
observable and is not the Stokes GP transform

\[
\operatorname{GP}_u(a,s)
=
\frac2{\Gamma(s)}
\sum_{k\ne0}\lambda_k^{s-1}e^{-a\lambda_k}|\widehat u(k)|^2.
\]

```text
T5=A_H@c6b95 GP/Widder interface + OPEN Stokes spectral instantiation
```

---

# T6. `H12_BKQR_FINITE_DIFFERENCE_REPRESENTATION`

## Methlib half-moment chain

The package-2 register records the following modules as externally audited
A-tier:

```text
CEA07A_BKQRHalfMomentCore
CEA07B_BKQRFiniteSpectralLift
CEA07C_BKQRCriticalWeight
CEA07D_StokesSpectralDictionary
CEA07E_TorusParseval
CEA07F_TorusStokesQuarter
```

The reusable inequalities include

\[
1+ax\le m(x)^2\le1+a^2x,
\]

and

\[
1+\sqrt x\le2m(x),
\qquad
m(x)\le a(1+\sqrt x).
\]

`CEA07G_BKQRActualHalfProduct` remains an A-tier candidate until matching
external compiler and theorem-level axiom-audit evidence exists.

## Pinned HVR defect-square chain

```lean
ORBIT_DEPTH_ENERGY_LE_BASE
HOPF_DEFECT_NONNEGATIVE
GRAM_DEFECT_NONNEGATIVE
MOMENT_DEFECT_IS_BKQR_PAIR_SQUARE
MOMENT_DEFECT_NONNEGATIVE
MOMENT_SQ_LE_BASE_SQ
WIDDER_DEFECT_IS_BKQR_PAIR_SQUARE
```

Key identity:

\[
\mu_0(a)^2-\mu_n(a)^2
=
\operatorname{HopfDefect}_{a,n}
+
\operatorname{GramDefect}_{a,n},
\]

with both channels represented by explicit squares.

Further reusable declarations:

```lean
WEIGHTED_COEFF_BOUND_IMPLIES_SUMMABLE_AT_SMALLER_RADIUS
CONTRACTIVE_ORBIT_GIVES_WEIGHTED_CAYLEY_COEFF_BOUND
CONTRACTIVE_ORBIT_FRONTIER_IMPLIES_STRICT_BKQR_PI_COEFF
contractiveOrbit_absolute_summability
```

## Missing actual finite-difference core

```lean
bkqrDelta (h : ℝ) := (I - poisson h) / h
bkqrDelta_nonneg
bkqrDelta_le_stokesSqrt
bkqrDelta_pow_binomial
bkqrDelta_tendsto_stokesPow
bkqrCriticalEnergyApprox
bkqrMoment_hankel_psd
```

Required exact identity:

\[
\left(\frac{I-Q_h}{h}\right)^nQ_a
=
h^{-n}\sum_{j=0}^{n}(-1)^j\binom njQ_{a+jh}.
\]

```text
T6=A_M + A_H@c6b95 + OPEN actual finite-difference operator
```

---

# T7. `H12_CAYLEY_STURMION_REPRESENTATION`

## Reusable interface and moment geometry

```lean
CayleyMomentCodec
BKQRCayleyModel
GPBKQRCommonMomentIdentity
GPCayleyTransferMatch
cayleyRadiusAtMetricDepth
metricDepthOfCayleyRadius
CAYLEY_RADIUS_AT_METRIC_DEPTH_NONNEG
CAYLEY_RADIUS_STRICT_MONO_SUBPI
CAYLEY_RADIUS_POS_OF_POS_SUBPI
CAYLEY_RADIUS_LE_ONE_SUBPI
```

The contractive-orbit defect and absolute-convergence theorems become usable
once the actual Stokes Cayley operator is supplied.

The existing `actualThetaCayleyObservable` is not the required operator

\[
C_\rho=(L-\rho I)(L+\rho I)^{-1}.
\]

It contributes an observable-interface pattern only.

## Missing exact core

```lean
stokesCayley
stokesCayley_selfAdjoint
stokesCayley_contracts
stokesCayley_resolvent_identity
stokesSturmion
stokesSturmion_chebyshev_recurrence
stokesSturmion_recover
stokesCayley_critical_readout
stokesCayley_moment_psd
```

```text
T7=A_H@c6b95 interface/moment scaffold + OPEN Stokes Cayley core
```

---

# T8. `H12_RESOLVENT_HVR_REPRESENTATION`

## Audited scalar resolvent calculus

Pinned sources:

- [`RH_HilbertLimit/TwoRoutes/ResolventAnalytic.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/RH_HilbertLimit/TwoRoutes/ResolventAnalytic.lean)
- [`RH_HilbertLimit/TwoRoutes/MeasureResolvent.lean`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/blob/c6b95fd9e3d792270026da083bddddbc72bacb22/RH_HilbertLimit/TwoRoutes/MeasureResolvent.lean)

```lean
denominator
kernel
transform
domain
continuous_kernel
exists_local_lower_bound
isOpen_domain
kernel_norm_le
hasDerivAt_kernel
integrable_kernel
hasDerivAt_transform
deriv_transform
analyticAt_transform
analyticOnNhd_transform
resolvent
transform_zero
iteratedDeriv_resolvent
analyticAt_resolvent
resolvent_eq_integral_positiveKernel
resolvent_im_nonpos
```

Mathlib also supplies bounded-algebra `resolventSet` infrastructure and
resolvent derivative theorems. This does not directly provide the unbounded
Stokes operator realization.

## Missing vector Stokes resolvent

```lean
stokesResolvent (μ : ℝ) : H12Datum → H12Datum
stokesResolvent_identity
stokesResolvent_contracts
stokesResolvent_commutes
stokesResolvent_recovery
stokesResolvent_completelyMonotone
stokesResolvent_critical_stieltjes
```

Principal endpoints:

\[
\mu(A+\mu I)^{-1}u\longrightarrow u,
\]

and

\[
q(u)
=
\frac1\pi
\int_0^\infty
\mu^{-1/2}
\left\langle u,A(A+\mu I)^{-1}u\right\rangle d\mu.
\]

```text
T8=A_H@c6b95 scalar resolvent calculus + OPEN vector Stokes resolvent
```

---

# T9. `H12_PHYSICAL_SPACE_REALIZATION`

## Directly reusable realization layer

Mathlib supplies forward torus Parseval:

```lean
hasSum_sq_mFourierCoeff
```

Methlib specializes this to finite scalar and vector support:

```lean
torus_scalar_finite_parseval
torus3_vector_finite_parseval
torus3_l2_dictionary_field
torus3_l2_spectral_eq_physical
torus3_stokes_quarter_dictionary
```

The package-1 status register also records compiled physical adapters:

```text
NSE_PHYSICAL_LP_DATA_CONSTRUCTION
PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS
```

## Missing inverse realization

Parseval begins with an existing physical \(L^2\) field. The representation
target begins with arbitrary admissible Fourier coefficients and must construct
the field.

```lean
fourierSynthesisH12
fourierExtractionH12
fourierExtraction_synthesis
fourierSynthesis_extraction
synthesis_real_iff_fourierReal
synthesis_divFree_iff_solenoidal
synthesis_meanZero_iff_zeroMode
synthesis_hhalfSq_eq
```

Missing seam:

\[
\ell^2\text{-coefficient datum}
\longrightarrow
L^2(\mathbb T^3),
\]

together with the reality and distributional-divergence dictionaries.

```text
T9=A_M forward/finite realization + OPEN inverse infinite synthesis
```

---

# T10. `H12_GP_BOREL_TWO_PARAMETER_REPRESENTATION`

## Existing general infrastructure

Mathlib supplies Bochner commutation with continuous linear maps:

```lean
ContinuousLinearMap.integral_comp_comm
```

and dominated differentiation under parameter integrals. The HVR resolvent
modules already instantiate this analytic infrastructure in a compiled
transform context.

The `stokes-conditional` repository records a conditional
Leray–Hopf → GP/BKQR → M7 → Serrin chain. Its current Lean package is retained
as a binary archive rather than directly importable source files in that
repository root; declaration-level reuse was therefore not established by this
scout.

## Missing exact core

```lean
BorelLaplaceOrbit
GPBorelKernel
GPBorelRepresentationCertificate
gpBorel_reconstruction
gpBorel_poisson_commutation
gpBorel_iterated_spatial_deriv
gpBorel_recover_at_zero
gpBorel_small_range
```

Target reconstruction:

\[
Q_a u(t_0+z)
=
Q_a u(t_0)
+
\int_0^\infty e^{-p/z}Q_aU(p)\,dp.
\]

This class depends structurally on T3 and T5.

```text
T10=Mathlib infrastructure + OPEN conditional representation core
```

---

# Dependency-adjusted implementation order

\[
\boxed{
T4
\longrightarrow
T1
\longrightarrow
T2
\longrightarrow
T9
\longrightarrow
T3
\longrightarrow
T6
\longrightarrow
T5
\longrightarrow
T8
\longrightarrow
T7
\longrightarrow
T10
}
\]

Equivalently:

```text
STAGE_I   = HEAT + GALERKIN + STOKES + PHYSICAL
STAGE_II  = POISSON + BKQR + GP
STAGE_III = RESOLVENT + CAYLEY
STAGE_IV  = GP_BOREL
```

# Principal conclusion

```text
T4  has an actual H12 implementation core already compiled.
T6  has the strongest existing cross-branch theorem library.
T1,T2,T9 have strong finite spectral or physical cores.
T3,T5,T7,T8 have audited abstract or scalar scaffolds only.
T10 requires a new conditional representation core.
```

The first implementation package should contain

```text
H12_HEAT_REPRESENTATION_COMPLETION
H12_FINITE_GALERKIN_CORE
H12_STOKES_QUARTER_DOMAIN_ADAPTER
H12_PHYSICAL_FINITE_REALIZATION_ADAPTER
```

followed by thin restriction modules for the five-class \(H^{1/2}\) lattice.
Prepared source must remain `A_TIER_CANDIDATE` until matching external native
compilation and theorem-level axiom-audit evidence exists.