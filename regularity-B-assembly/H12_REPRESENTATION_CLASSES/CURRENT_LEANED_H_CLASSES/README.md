# Current Leaned \(H\)-Classes

```text
REGISTER_SCOPE=PERIODIC_CRITICAL_H12
CURRENT_EXACT_CARRIER=H12FourierFoundations.H12Datum
ROOT_SOURCE=regularity-B-assembly/pkg1/H12_FOURIER_FOUNDATIONS.lean
LEAN_EXECUTION_FOR_THIS_REGISTER=NONE
```

## 1. Exact current Lean carrier

The presently defined critical carrier is

```lean
H12FourierFoundations.H12Datum
```

with fields

```lean
coeff          : Mode3 → CVec3
meanZero       : coeff 0 = 0
solenoidal     : ∀ k, SolenoidalAt k (coeff k)
hhalfSummable  : Summable (hhalfTerm coeff)
```

Consequently, the exact mathematical class represented by the current carrier is

\[
H^{1/2}_{\sigma,0}(\mathbb T^3;\mathbb C^3),
\]

where the homogeneous critical coefficient functional is

\[
q(u)=\sum_{k\in\mathbb Z^3}(2\pi |k|)\,|\widehat u(k)|^2.
\]

The real-valued conjugation symmetry is not presently a field of `H12Datum`.
Thus the carrier is the complexified mean-zero solenoidal class; the real
subspace remains a subsequent restriction.

## 2. Current class lattice

| Mathematical class | Current Lean realization | Formal state |
|---|---|---|
| \(H^{1/2}\) | The coefficient density `hhalfTerm` and total functional `hhalfSq` exist; no separate unconstrained carrier is presently defined. | structural core available |
| \(H^{1/2}_{\sigma}\) | Solenoidality exists as `SolenoidalAt` and as the field `H12Datum.solenoidal`; no separate non-mean-zero subtype is presently defined. | restriction encoded, standalone carrier open |
| \(H^{1/2}_{\sigma,0}\) | `H12FourierFoundations.H12Datum`. | exact current carrier |
| \(H^{1/2}_{\sigma,\mathrm{small}}\) | Smallness occurs in the critical-absorption theorem layer; no standalone audited carrier was located. | subtype split open |
| \(H^{1/2}_{\sigma,0,\mathrm{small}}(\nu)\) | Root B-tier regularity target with threshold recorded in `pkg1/STATUS.txt`; no standalone audited carrier was located. | B-tier target; carrier split open |

The current five-class representation grid must therefore be interpreted as a
restriction lattice over one compiled carrier, not as five already distinct Lean
types.

## 3. Compiled structural declarations

### Fourier and solenoidal foundation

Source: [`../../pkg1/H12_FOURIER_FOUNDATIONS.lean`](../../pkg1/H12_FOURIER_FOUNDATIONS.lean)

```lean
Mode3
RVec3
CVec3
modeReal
modeComplex
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
hhalfTerm
hthreeHalfTerm
H12Datum
```

### Heat-stable carrier structure

Source: [`../../pkg1/H12_FOURIER_FOUNDATIONS.lean`](../../pkg1/H12_FOURIER_FOUNDATIONS.lean)

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

The declaration `heatDatum` maps an `H12Datum` to an `H12Datum` for
nonnegative viscosity and time.

### Critical spectral energy

Source: [`../../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean`](../../pkg1/H12_SPECTRAL_ENERGY_BRIDGE.lean)

```lean
hhalfSq
honeTerm
hhalfFinset
honeFinset
hthreeHalfFinset
honeTerm_sq_eq_hhalf_mul_hthreeHalf
finite_critical_interpolation
hhalfSq_nonneg
heat_hhalfSq_le
SpectralEnergyBundle
H12_SPECTRAL_ENERGY_BRIDGE
```

The principal finite interpolation theorem is

\[
E_{1,N}(u)^2
\le
E_{1/2,N}(u)E_{3/2,N}(u).
\]

The principal semigroup inequality is

\[
q(e^{-\nu tA}u)\le q(u).
\]

## 4. Current regularity status

Source: [`../../pkg1/STATUS.txt`](../../pkg1/STATUS.txt)

The status register records external native PASS and approved theorem-level
axiom sets for the following structural modules:

```text
H12_FOURIER_FOUNDATIONS
H12_SPECTRAL_ENERGY_BRIDGE
H12_CRITICAL_ABSORPTION
H12_CRITICAL_TRILINEAR_COMPILER
H12_HOLDER_LP_ADAPTER
NSE_POINTWISE_PAIRING_IDENTIFICATION
NSE_PAIRING_POINTWISE_LP_LIFT
NSE_PHYSICAL_LP_DATA_CONSTRUCTION
PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS
```

The current B-tier root theorem is

```text
H12_SIGMA_SMALL_GLOBAL_REGULARITY
```

with recorded threshold

\[
\|u_0\|_{\dot H^{1/2}}<\frac{\nu}{8C_3^3}.
\]

Its unresolved analytic and PDE interfaces remain

```text
PeriodicHhalfL3
H12_LOCAL_CONTINUATION
H12_SIGMA_SMALL_GLOBAL_REGULARITY root compiler
```

Therefore the small-data global-regularity conclusion is not reclassified here
as an unconditional A-tier root theorem.

## 5. Required next subtype declarations

The minimal nonduplicative class split is

```lean
H12Carrier
H12Sigma
H12SigmaZero
H12SigmaSmall (ν : ℝ)
H12SigmaZeroSmall (ν : ℝ)
```

with explicit coercions and equivalences

```lean
H12SigmaZero ≃ H12FourierFoundations.H12Datum
H12SigmaZeroSmall ν ≃ {u : H12Datum // SmallH12 ν u}
```

These names are design endpoints only. They are not declared or promoted by
this register.