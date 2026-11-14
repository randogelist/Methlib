# Round 05 — Reuse Boundary

## 1. Frozen reusable kernels

The following layers should remain unchanged and be imported by the frontier
spine.

### Carrier and Fourier realization

```text
CriticalSpaces
CriticalSpacesCutoff
CriticalSpacesEmbedding
CriticalInitialPhysicalFourier
```

### Finite NSE/Galerkin construction

```text
CriticalGalerkin
CriticalGalerkinTrajectory
GalerkinExistence
GalerkinInvariant
```

### Parameterized scalar analysis

```text
CriticalInvariant
CriticalPositiveTimeEnergy
LinearBudget
DissipativeODE
```

`CriticalInvariant` is especially important: its principal theorems already
accept an arbitrary coefficient `C` and strict gap `C * a0 < ν`.

### Compactness and trace kernels

```text
CriticalLimit*
CriticalTrace*
CountableCompactExtraction
SobolevTimeL2Compactness
```

### Physical positive-time realization

```text
CriticalPositiveFlow
CriticalPositiveLimitCalculus
PhysicalNSEIdentity
PeriodicPressureRecovery
```

### Physical class and uniqueness kernels

```text
CriticalGlobalSerrin
CriticalStrongLerayHopf
CriticalSerrinUniqueness
CriticalClassicalWeakMomentum
```

These kernels consume bounds or solution records. They do not intrinsically
select `criticalNonlinearConstant`.

## 2. Constant-sensitive wrappers

The following modules either define the current coefficient, hard-code its
smallness premise, or hard-code denominators containing it.

```text
CriticalNonlinear
SmallDataAX6Closure
CriticalTimeDerivative
CriticalUniformBounds
CriticalPositiveTimeSeed
CriticalPositiveTimeHighOrder
CriticalPositiveLimit
CriticalPhysicalQuantitative
SmallDataRoot
SmallDataQuantitative
CriticalGlobalEnergyClass
SmallDataSerrin
SmallDataUniqueness
NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
SmallDataClosure
```

Not every theorem in these files must be duplicated. The index classifies at
theorem level during implementation.

## 3. New analytic edge

The minimal genuinely new estimate is

```lean
frontierNonlinearBound :
  ∀ N c,
    supportCondition N c ->
    SpectralReality c ->
    SpectralSolenoidal c ->
    |criticalNonlinearPower 1 N c| <=
      frontierNonlinearConstant *
        Real.sqrt (criticalEnergy 1 N c) *
        criticalEnergy 3 N c
```

Without this theorem, a larger centered ball is not derivable.

## 4. New wrapper kernel

After `frontierNonlinearBound`, define frontier analogues only where the old
constant is syntactically fixed:

```text
frontier critical differential inequality
frontier Galerkin invariant
frontier dissipation budget
frontier sharp quartic budget
frontier time-derivative budget
frontier compactness input package
frontier positive-time seed
frontier quantitative solution wrapper
frontier final root
```

The underlying compactness, trace, physical NSE, and uniqueness proofs should
be invoked unchanged.

## 5. Namespace rule

All new declarations use:

```lean
namespace SingularClosure.H12Frontier
```

Existing types are referenced fully or through controlled `open` statements.
No new declaration shall shadow:

```text
criticalNonlinearConstant
criticalDissipationBudget
criticalTimeDerivativeBudget
NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

Proposed frontier names:

```text
frontierNonlinearConstant
frontierDissipationBudget
frontierTimeDerivativeBudget
NSE_H12_FRONTIER_UNCONDITIONAL
```

## 6. Refactor policy

Preferred order:

```text
thin frontier wrappers
  -> prove successful external build
  -> identify duplicated theorem bodies
  -> only then extract generic parameterized infrastructure
```

A large refactor before the first frontier root would unnecessarily place the
already certified base at risk.

## 7. Base regression law

Every frontier build must still compile and audit

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

with its original exact type. Frontier success cannot compensate for a base
regression.