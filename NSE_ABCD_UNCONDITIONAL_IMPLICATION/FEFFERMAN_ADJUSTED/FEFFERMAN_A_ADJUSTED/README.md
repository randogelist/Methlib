# Fefferman adjusted A

For every admissible positive-time state of an exhibited small unforced flow, the time-shifted velocity and pressure give a global unforced solution. Constructing the ancestor flow from a small seed alone remains open in Lean.

## Native verification

| Field | Value |
| --- | --- |
| Release | `FEF_A_POSITIVE_TIME_433` |
| Theorem | `Fefferman.ConcreteReal.AdjustedA.FEF_A_POSITIVE_TIME` |
| Type | `∀ ε : ℝ, Fefferman_adjusted_A ε` |
| Compiler | Native Windows Lean 4.33.0 |
| Run ID | `r-4e391a4e536f42a9bec4df892ed60ef5` |
| Result | `PROJECT_BUILD=PASS`, `RUN=PASS` |
| Audit | 12 theorem reports, all standard-only |

The source manifest records the candidate status at packaging time. The table records the subsequent external run.

Run `run.cmd` from this directory on Windows with cached Mathlib. The ZIP contains the same source package in its original release layout.
