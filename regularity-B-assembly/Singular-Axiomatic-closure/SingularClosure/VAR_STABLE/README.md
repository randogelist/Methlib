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

Existing dependencies are collected in:

```text
SingularClosure/VAR_STABLE/Endpoints/
```

The aggregate import is:

```lean
import SingularClosure.VAR_STABLE.Endpoints.All
```

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

## Endpoint groups

```text
Endpoints/Mathlib.lean
Endpoints/AX6.lean
Endpoints/Critical.lean
Endpoints/Channels.lean
Endpoints/Galerkin.lean
Endpoints/Limit.lean
Endpoints/Entry.lean
Endpoints/All.lean
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

## Status

```text
Endpoint gathering only.
No local Lean execution.
No external compiler transcript.
No theorem-level axiom audit.
No A_TIER promotion.
```
