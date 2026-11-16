# VAR_STABLE endpoint staging

## Repository state

- Branch: `VAR_STABLE`
- Base branch: `VAR_STABLE_COSNTRUCT`
- Base commit: `59a16306ae1a37906e2ad86bfcd93af57089d08e`
- Lean toolchain: `v4.33.0`
- Mathlib revision: `db584cd6d46c92f209a44c0f1c829460d327499d`

## Scope

This directory is the isolated staging location for the finite-horizon
`VAR_STABLE` construction.

No declaration in this directory is classified as proved merely by being
prepared. Promotion requires a matching external native Lean build and a
theorem-level axiom audit.

## Primary root target

```text
FINITE_ENTRY_AX6_IMP_GLOBAL_REGULARITY
```

Target implication:

```text
AX6At(ν, a, T_entry(ν, a))
  -> GlobalRegularity(ν, a)
```

## Dependency spine

```text
AX6At
  -> LOCAL_AX6_TO_STRONG_SOLUTION_THROUGH
  -> CRITICAL_ENERGY_ZERO_ONE_TWO_INTERPOLATION
  -> EXPLICIT_CRITICAL_ENTRY_HORIZON
  -> STRONG_TRACE_TO_CRITICAL_DATUM
  -> SMALL_CRITICAL_SOLUTION_TIME_SHIFT
  -> SMALL_CRITICAL_RESTART_SPLICE
  -> FINITE_ENTRY_AX6_IMP_GLOBAL_REGULARITY
```

## Planned module order

```text
01_AX6At.lean
02_AX6AtCanonical.lean
03_LocalExactBudget.lean
04_LocalStrongBounds.lean
05_LocalCompactness.lean
06_LocalStrongLimit.lean
07_ZeroOneTwoInterpolation.lean
08_LocalEnergyDecay.lean
09_GoodRestartTime.lean
10_EntryHorizon.lean
11_SmoothTraceCriticalDatum.lean
12_SmallSolutionShift.lean
13_RestartSplice.lean
14_EntryGlobalRoot.lean
15_FiniteHeadGronwall.lean
16_EntryHeadTailCertificate.lean
17_EntryChecker.lean
18_OptionalQFBMinHorizon.lean
19_RoughLerayHopfEntry.lean
20_Root.lean
```

## Initial endpoint register

### Local AX6 interface

```text
AX6At
AX6At_iff_selected_AX6Statement_instance
AX6At_iff_canonical
AX6_AT_EXACT_REAL_SQUARE_BUDGET
AX6_AT_UNIFORM_ENSTROPHY_ACCUMULATION
AX6_AT_UNIFORM_TIME_DERIVATIVE_BOUND
AX6_AT_UNIFORM_PHYSICAL_STRONG_BOUNDS
```

### Finite-horizon solution

```text
StrongSolutionThrough
LOCAL_AX6_H0_L2H1_SUBSEQUENCE
LOCAL_AX6_STRONG_INITIAL_TRACE
LOCAL_AX6_TO_STRONG_SOLUTION_THROUGH
LOCAL_AX6_POSITIVE_TIME_ALL_ORDERS
LOCAL_AX6_POSITIVE_SMOOTH_NSE
```

### Entry-horizon reduction

```text
CRITICAL_ENERGY_ZERO_ONE_TWO_INTERPOLATION
CRITICAL_HHALF_NORM_LE_L2_H1_GEOMETRIC_MEAN
STRONG_SOLUTION_L2_EXPONENTIAL_DECAY
STRONG_SOLUTION_GOOD_H1_TIME
EXPLICIT_CRITICAL_ENTRY_HORIZON
POINCARE_GAP_ENTRY_HORIZON
```

### Critical restart

```text
STRONG_TRACE_TO_CRITICAL_DATUM
SMALL_CRITICAL_SOLUTION_TIME_SHIFT
LOCAL_STRONG_SMALL_CRITICAL_OVERLAP_UNIQUE
SMALL_CRITICAL_RESTART_SPLICE
```

### Root

```text
FINITE_ENTRY_AX6_IMP_GLOBAL_REGULARITY
AX6_ENTRY_UNIVERSAL_IMP_FEFFERMAN_B
FEFFERMAN_B_REDUCES_TO_ENTRY_HORIZON
```

## Status

```text
B_TIER staging only.
No local Lean execution.
No external compiler transcript.
No theorem-level axiom audit.
No A_TIER promotion.
```
