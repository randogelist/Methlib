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

## Build and theorem audit

This directory is a Lean 4.33.0 Lake project. It contains the v0.25.0 theorem source and its two project imports, copied byte-for-byte from the v0.11.0 base package. The manifest pins Mathlib to `db584cd6d46c92f209a44c0f1c829460d327499d`.

| Verification | Evidence |
| --- | --- |
| Build the extracted source | `lake build ConcreteABCDUnifiedClosure` |
| Re-import the compiled theorem and typecheck its forward implication | `lake env lean ci/Audit.lean` |
| Audit the six named declarations | Exactly one report per declaration, with axioms contained in `{propext, Classical.choice, Quot.sound}` |

GitHub Actions runs on changes to this directory or its workflow, and by manual dispatch. Each run publishes the tested revision, source hashes, compiler version, build log and theorem-level reports. [Workflow](../../.github/workflows/nse-abcd-implication.yml) · [CI runs](https://github.com/randogelist/Methlib/actions/workflows/nse-abcd-implication.yml)

**Native Windows** · With Git, elan and Python 3 installed, run `call run.cmd` from this directory. The runner uses the pinned Lake dependencies and precompiled Mathlib cache. [Windows runner](run.cmd)

**Source provenance** · [Original v0.25.0 ZIP](https://raw.githubusercontent.com/randogelist/Methlib/a10286aedbe60e344fff4327237bf90ac551b281/NSE_ABCD_UNCONDITIONAL_IMPLICATION/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0.zip) · [Original package notes](README.txt)

| Original source archive | SHA-256 |
| --- | --- |
| v0.25.0 unified closure | `463dec3a7e1638c5e078dcfe732a9648a8ed129ce3dc7ec54b9aaa949b42e19c` |
| v0.11.0 two-layer base | `bddd0a0b0a6a38b343002bf141e902bfb1cf8664770e910882778f4037bdefb8` |
