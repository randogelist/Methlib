# NSE_ABCD_UNCONDITIONAL_IMPLICATION

The v0.25.0 Lean package gives an unconditional implication to the **full Fefferman list** in `Fefferman.ConcreteReal`. Its conclusion is conditional on constructing a proof of `ABCDPhysicalPort`.

```lean
ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD :
  ABCDPhysicalPort ↔
    (A realAnalysis ∧ B realAnalysis ∧ C realAnalysis ∧ D realAnalysis)
```

Given `p : ABCDPhysicalPort`, the proof of the conjunction is `ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD.mp p`. The reverse direction recovers the port from the conjunction. [Lean theorem](Fefferman_A/ConcreteABCDUnifiedClosure.lean#L3022)

## Fefferman list

| Project | Endpoint | Construction premise |
| --- | --- | --- |
| [Fefferman A](Fefferman_A/) | Whole-space regularity at zero force | `WholeSpaceZeroForceGlobalRegularity` |
| [Fefferman B](Fefferman_B/) | Periodic regularity at zero force | `PeriodicZeroForceGlobalRegularity` |
| [Fefferman C](Fefferman_C/) | Whole-space forced breakdown | `WholeSpaceForcedBreakdown` |
| [Fefferman D](Fefferman_D/) | Periodic forced breakdown | `PeriodicForcedBreakdown` |

Each directory is a standalone Lean 4.33.0 project with its own copy of the complete proof source, local imports, pinned Lake manifest, Windows runner and theorem audit. Copy any one directory to build it independently. The four construction premises remain open in v0.25.0.

CI builds each committed endpoint directory in isolation, audits its two named endpoint declarations and the six unified declarations, and publishes a standalone source ZIP and evidence for each endpoint. [Workflow](../../.github/workflows/nse-abcd-implication.yml) · [CI runs](https://github.com/randogelist/Methlib/actions/workflows/nse-abcd-implication.yml)

**Source provenance** · [Original v0.25.0 ZIP](https://raw.githubusercontent.com/randogelist/Methlib/a10286aedbe60e344fff4327237bf90ac551b281/NSE_ABCD_UNCONDITIONAL_IMPLICATION/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0.zip) · [Original package notes](Fefferman_A/README.txt)

| Original source archive | SHA-256 |
| --- | --- |
| v0.25.0 unified closure | `463dec3a7e1638c5e078dcfe732a9648a8ed129ce3dc7ec54b9aaa949b42e19c` |
| v0.11.0 two-layer base | `bddd0a0b0a6a38b343002bf141e902bfb1cf8664770e910882778f4037bdefb8` |
