# NSE_ABCD_UNCONDITIONAL_IMPLICATION

The v0.25.0 Lean package gives an unconditional implication to the **full Fefferman list** in `Fefferman.ConcreteReal`. Its conclusion is conditional on constructing a proof of `ABCDPhysicalPort`.

```lean
ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD :
  ABCDPhysicalPort ↔
    (A realAnalysis ∧ B realAnalysis ∧ C realAnalysis ∧ D realAnalysis)
```

Given `p : ABCDPhysicalPort`, the proof of the conjunction is `ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD.mp p`. The reverse direction recovers the port from the conjunction. [Lean theorem](ConcreteABCDUnifiedClosure.lean#L3022)

## Construction of the four endpoints

| Clause | Field of `ABCDPhysicalPort` | Proposition required |
| --- | --- | --- |
| A | `wholeSpaceRegular` | `WholeSpaceZeroForceGlobalRegularity` |
| B | `periodicRegular` | `PeriodicZeroForceGlobalRegularity` |
| C | `wholeSpaceBreakdown` | `WholeSpaceForcedBreakdown` |
| D | `periodicBreakdown` | `PeriodicForcedBreakdown` |

For A and B, every positive viscosity and every admissible initial datum must admit a global solution at zero force on the indicated domain. For C and D, at each positive viscosity one must exhibit admissible initial data and an admissible force for which no global solution exists on that domain. The construction of these four fields remains open in this package. [Lean structure](ConcreteABCDUnifiedClosure.lean#L2972)

## Package and external verification

[Download the original v0.25.0 ZIP](https://raw.githubusercontent.com/randogelist/Methlib/main/NSE_ABCD_UNCONDITIONAL_IMPLICATION/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0.zip) · [Package notes](README.txt) · [Windows runner](run.cmd)

| Native Windows prerequisite | Value |
| --- | --- |
| Lean | `4.33.0` |
| Compiled Mathlib cache | Under `%USERPROFILE%\lean-native`, matching Lean 4.33.0 |
| Base package | `%USERPROFILE%\Downloads\FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0.zip` |

From the directory containing `ConcreteABCDUnifiedClosure.lean`, run `call run.cmd`. The runner recreates its versioned worktree under Downloads. The theorem-level `#print axioms` output is written to `concrete_build\ConcreteABCDUnifiedClosure.log` in that worktree. The published archive contains the Lean source, the runner and the original package notes. The external compiler and theorem-level audit log must be supplied separately for A-tier verification.

Archive SHA-256: `463dec3a7e1638c5e078dcfe732a9648a8ed129ce3dc7ec54b9aaa949b42e19c`.
