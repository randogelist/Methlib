# VAR_STABLE gathered endpoints

This directory gathers the existing dependencies selected for the new
`VAR_STABLE` proof branch. The Lean files are import-and-`#check` modules only.
They do not prove any of the planned `VAR_STABLE` endpoints.

## Modules

| Module | Role |
|---|---|
| `Mathlib.lean` | Gronwall, approximate ODE trajectories, fixed points, local flows, partitions of unity |
| `AX6.lean` | AX6 admission, exact budget, strong bounds, all-order bootstrap, global root |
| `Critical.lean` | Critical interpolation, nonlinear and negative-order estimates, relative energy, small data |
| `Channels.lean` | Six-channel reconstruction, orthogonality, weighted Pythagoras, physical/spectral identification |
| `Galerkin.lean` | Finite Galerkin vector field, existence, uniqueness, canonical path, energy, Poincare |
| `Limit.lean` | Time compactness, Fatou, terminal dissipation, positive flow, strong limit, smoothness, pressure |
| `Entry.lean` | Entry-horizon inputs and unconditional small-critical tail |
| `All.lean` | Aggregate import |

## Existing endpoint spine

```text
finite certificate
  -> selected-horizon AX6 budget
  -> localized strong bounds
  -> finite-horizon strong solution
  -> explicit entry horizon
  -> small critical trace
  -> unconditional small-data tail
  -> global regularity
```

## Planned new declarations

```text
AX6At
AX6At_iff_canonical
LOCAL_AX6_TO_STRONG_SOLUTION_THROUGH
CRITICAL_ENERGY_ZERO_ONE_TWO_INTERPOLATION
EXPLICIT_CRITICAL_ENTRY_HORIZON
STRONG_TRACE_TO_CRITICAL_DATUM
SMALL_CRITICAL_SOLUTION_TIME_SHIFT
SMALL_CRITICAL_RESTART_SPLICE
FINITE_ENTRY_AX6_IMP_GLOBAL_REGULARITY
```

## Status

```text
Endpoint gathering only.
No local Lean execution.
No external compiler transcript.
No theorem-level axiom audit.
No A_TIER promotion.
```
