# Round 06 — Frontier Extension DAG

## 1. Proposed source tree

```text
SingularClosure/
└─ H12Frontier/
   ├─ Contracts.lean
   ├─ LiteratureConstants.lean
   ├─ Normalization.lean
   ├─ ConstantComparison.lean
   ├─ NonlinearBound.lean
   ├─ DifferentialInequality.lean
   ├─ Invariant.lean
   ├─ Budgets.lean
   ├─ TimeDerivative.lean
   ├─ Compactness.lean
   ├─ PositiveTime.lean
   ├─ Quantitative.lean
   ├─ LerayHopf.lean
   ├─ Root.lean
   └─ Closure.lean
```

Aggregate module:

```text
SingularClosure/H12Frontier.lean
```

## 2. Dependency graph

```text
Contracts
  -> LiteratureConstants
  -> Normalization
  -> ConstantComparison

CriticalEnergy + CriticalSobolev + CriticalNonlinear
  -> NonlinearBound

NonlinearBound + CriticalInvariant
  -> DifferentialInequality
  -> Invariant
  -> Budgets

Budgets + CriticalTimeDerivative kernels
  -> TimeDerivative

Budgets + TimeDerivative + CriticalLimit kernels
  -> Compactness

Compactness + CriticalTrace kernels + CriticalPositiveTime kernels
  -> PositiveTime

PositiveTime + CriticalPhysicalQuantitative + CriticalGlobalEnergyClass kernels
  -> Quantitative

Quantitative + CriticalGlobalSerrin + CriticalStrongLerayHopf
  -> LerayHopf

LerayHopf + base physical endpoint types
  -> Root
  -> Closure
```

## 3. Contract layer

Suggested records:

```lean
structure FrontierConstantData where
  K2 : ℝ
  K2_pos : 0 < K2

structure FrontierNonlinearCertificate
    (D : FrontierConstantData) : Prop where
  bound : ∀ N c,
    SupportAt N c ->
    SpectralReality c ->
    SpectralSolenoidal c ->
    |criticalNonlinearPower 1 N c| <=
      (D.K2 / Real.sqrt 2) *
        Real.sqrt (criticalEnergy 1 N c) *
        criticalEnergy 3 N c
```

Exact support predicate shall reuse the existing support function rather than
introduce an inequivalent carrier.

## 4. Normalization endpoint

```lean
frontierNonlinearConstant (D : FrontierConstantData) : ℝ :=
  D.K2 / Real.sqrt 2

frontierNonlinearConstant_pos
frontier_radius_eq_sqrtTwo_div
```

The second theorem should express

```text
(frontierNonlinearConstant D)^(-1) = sqrt 2 / D.K2
```

under `D.K2_pos`.

## 5. Analytic endpoint

Preferred exact target:

```lean
FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND :
  ∃ K2 : ℝ, 0 < K2 ∧
    ∀ N c, SupportAt N c ->
      SpectralReality c -> SpectralSolenoidal c ->
      |criticalNonlinearPower 1 N c| <=
        (K2 / Real.sqrt 2) *
          Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c
```

This theorem must not be replaced by an opaque premise in an unconditional
root.

## 6. Invariant endpoint

```lean
FRONTIER_CRITICAL_ENERGY_INVARIANT
FRONTIER_CRITICAL_DISSIPATION_BUDGET
FRONTIER_CRITICAL_SHARP_QUARTIC_BUDGET
```

These should be thin instantiations of existing parameterized scalar theorems.

## 7. Physical root endpoint

Target theorem:

```lean
NSE_H12_FRONTIER_UNCONDITIONAL
    (ν : ℝ) (hν : 0 < ν)
    (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : frontierNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a)
        U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      FrontierQuantitativeConclusions ν a U
```

`FrontierQuantitativeConclusions` may be a structure to prevent an oversized
root type while preserving every quantitative field.

## 8. Inclusion endpoints

Separate the following theorems:

```text
base_to_frontier_or_frontier_to_base
frontier_strictly_extends_base
frontier_extends_literal_literature_ball
```

Each requires a different constant inequality. None is bundled into the
physical root.

## 9. Proof-spine safety

Asynchronous elaboration may be enabled in ordinary source modules. Audit
modules must set asynchronous elaboration to false and check the final exact
root type and theorem axioms.