# Round 03 — Exact Proof Spine

## 1. Stage register

The unconditional root is assembled through the following certified stages.

| Stage | Principal modules | Output |
|---:|---|---|
| 1 | `CriticalSpaces`, `CriticalSpacesEmbedding` | actual half-integer Fourier Sobolev carriers and physical L² maps |
| 2 | `CriticalGalerkin`, `CriticalGalerkinTrajectory` | actual finite Galerkin trajectories for rough critical data |
| 3 | `CriticalSobolev`, `CriticalHolder` | cutoff-independent H^(1/2)→L³ and physical Holder bounds |
| 4 | `CriticalEnergy`, `CriticalNonlinear` | exact energy identity and uniform nonlinear estimate |
| 5 | `CriticalInvariant`, `SmallDataAX6Closure` | invariant critical ball, dissipation, quartic and AX6 budgets |
| 6 | `CriticalTimeDerivative`, `CriticalUniformBounds` | H^(-1/2) time budget and global compactness inputs |
| 7 | `CriticalLimit*` | one global Galerkin subsequence and limit representatives |
| 8 | `CriticalTrace*` | strong H^(1/2) initial trace |
| 9 | `CriticalPositiveTime*`, `CriticalPositiveLimit`, `CriticalPositiveFlow` | all-order positive-time flow and physical NSE |
| 10 | `SmallDataQuantitative`, `CriticalGlobalEnergyClass`, `CriticalGlobalSerrin`, `CriticalStrongLerayHopf`, `SmallDataUniqueness` | quantitative global class, Leray–Hopf membership, Serrin uniqueness |
| 11 | `SmallDataRoot`, `NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL`, `SmallDataClosure` | final physical root |

## 2. Root dependency chain

```text
CriticalSpaces
  -> CriticalGalerkin
  -> CriticalSobolev
  -> CriticalEnergy
  -> CriticalNonlinear
  -> SmallDataAX6Closure
  -> CriticalTimeDerivative
  -> CriticalUniformBounds
  -> CriticalLimitGlobal
  -> CriticalTraceStrong
  -> CriticalPositiveTimeHighOrder
  -> CriticalPositiveLimit
  -> SmallDataRoot
  -> SmallDataQuantitative
  -> CriticalGlobalEnergyClass
  -> CriticalGlobalSerrin
  -> CriticalStrongLerayHopf
  -> SmallDataUniqueness
  -> NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
  -> SmallDataClosure
```

The actual import DAG contains additional intermediate modules. This chain is
the minimal conceptual spine for frontier assembly.

## 3. Constant-sensitive section

The smallness constant first becomes concrete at

```lean
SingularClosure.criticalNonlinearConstant
```

in `SmallDataAX6Closure.lean`. It is selected from

```lean
FINITE_CRITICAL_NONLINEAR_BOUND
```

and drives:

```text
critical differential inequality
critical invariant
H^(3/2) dissipation budget
quartic gradient budget
H^(-1/2) time-derivative budget
positive-time seed
compactness constants
quantitative root denominators
```

## 4. Constant-independent continuation section

Once the required uniform bounds and coefficient convergence are supplied,
the following machinery is structurally independent of the numerical value of
the smallness constant:

```text
finite Galerkin existence
coefficient compactness
limit reconstruction
strong trace theorem
positive-time physical realization
pressure recovery
Serrin comparison theorem
Leray–Hopf record construction
weak–strong uniqueness theorem
```

These modules should be reused rather than copied again.

## 5. Extension attachment point

The frontier shall attach immediately before the current instantiation in
`SmallDataAX6Closure.lean`:

```text
new proved frontier nonlinear bound
  -> new frontier constant
  -> existing parameterized CRITICAL_ENERGY_INVARIANT
  -> frontier-specific budget wrappers
  -> existing compactness/trace/physical kernels
```

Attaching only at `SmallDataRoot` is insufficient for a genuinely larger ball,
because `SmallDataRoot` already requires the old constant condition.

## 6. Endpoint preservation

The frontier root should conclude the same physical structure as the base root.
Only the premise and constant-indexed quantitative budgets may differ. No
weakening to an abstract `CriticalGlobalRegularity` proposition is permitted at
the terminal endpoint.