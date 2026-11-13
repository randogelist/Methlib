# QFA assembly

```lean
import QFA.Assembly
```

```text
VERSION = 0.3.0
NEW_VERIFIED_THEOREMS = 20
LOCAL_INDICES = LE074-LE093
LEAN_STATUS = A_TIER
EXTERNAL_COMPILER_AND_AXIOM_AUDIT = PASS
LOCAL_LEAN_EXECUTIONS = 0
```

## Interfaces

| Module | Inputs | Outputs |
|---|---|---|
| [Representation.lean](Representation.lean) | Actual compact-test first/diagonal-second derivative witnesses and L2 Laplacian sum | Isometric complexified data; Schwartz/spectral targets conditional on LC004/LC001 |
| [Restart.lean](Restart.lean) | EnergyProfile, positive viscosity, strict cutoff, weak pairing continuity, a.e. Good and energy starts | Selected time, subcritical product, energy start, shifted EnergyProfile, weak continuity and strong initial trace |
| [AnalyticInputs.lean](AnalyticInputs.lean) | Actual norm readouts, derivative data, LC002/LC003, convection bound and enstrophy inequality | ScalarProfile, exact nonlinear bound, positive viscosity margin and absorption inequality |
| [Comparison.lean](Comparison.lean) | A.e. valid starts, common strong traces, continuous nonnegative coefficient, coefficient/product integrability and relative energy | Equality on positive/closed horizons and nonnegative time; restricted singleton with explicit reference membership |

## Exact interface restrictions

`CompactDerivativeData` supplies actual witnesses. Its existence is a
physical input. `CompactToSchwartzEndpoint` is LC004; its proof remains
pending. LE076 and LE077 retain the named analytic inputs in their types.

`RestartData` has three fields: shifted energy profile, weak pairing
continuity, and strong trace. The translated momentum equation and actual
LH membership require the subsequent AD02 construction.

The selected time supplies energy data. It does not itself supply H2
regularity or a Laplacian. The strong-solution construction provides those
later analytic inputs. The variable `d` requires identification with an
actual derivative; a pointwise positive margin requires the separate
time-invariant argument before continuation.

The comparison assembly derives the admissible sequence and its limiting
trace. Genuine integrability of the coefficient and relative-energy product
remains an input. Explicit initial values are required for equality at zero.
The singleton contains functions on `{t : ℝ // 0 ≤ t}`.

## Registers

- [QUASI_FEFFERMAN_A_ASSEMBLY_B_TIER.txt](../../QUASI_FEFFERMAN_A_ASSEMBLY_B_TIER.txt): complete mathematical derivations and exact signatures.
- [assembly-manifest.json](../../assembly-manifest.json): input/output interfaces and remaining physical stages AO01–AO08.
- [endpoint-manifest.json](../../endpoint-manifest.json): all 93 exact audit roots and source hashes.
- [Indexed frozen-root derivation](../../../QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt): entry points at their mathematical application steps.
- [run.cmd](../../run.cmd): cached external native Windows Lean 4.33.0 execution.

The frozen physical QFA root is unchanged and remains B_TIER.
LE074–LE093 are verified within the exact 93-root audit at commit
`97d745678734a2bb9d7c1d9d4ae05d1a36c0a162`. [Run 43528295686](https://github.com/randogelist/Methlib/actions/runs/43528295686), attempt 1;
[verified evidence](../../../CI/97d745678734a2bb9d7c1d9d4ae05d1a36c0a162/VERIFICATION.txt).
LC001–LC004 and AO01–AO08 remain unresolved. Source-header candidate
comments retain their preparation snapshot; the endpoint ledger records
the current exact declaration status.
