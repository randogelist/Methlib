# Quasi-Fefferman-B: R8 source preload

| Field | Value |
|---|---|
| Source revision | `R8` |
| Mathematical derivation | `R7`; `!=B_TIER` |
| Candidate source status | `A_TIER_CANDIDATE` |
| Root | `QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED : QuasiFeffermanBStatement` |
| Root / premise / cutoff changes | `0` |
| Candidate proof-source changes | `7` modules |
| Added public theorem statements | `0` |
| Added private helper | `1`; pairing derivative factorization |
| Upstream snapshots | `35` Lean files; `1` Mathlib license |
| Local Lean / Lake / compiler-version executions | `0` |
| R8 external runs / new A-tier promotions | `0 / 0` |

## Source indexes

| Index | Content |
|---|---|
| [upstream-sources.json](upstream-sources.json) | Exact source revisions, Git blob hashes, SHA256, paths, licenses |
| [upstream-api-index.json](upstream-api-index.json) | Fully qualified native names; declaration or generated-declaration origins |
| [qfb-api-index.json](qfb-api-index.json) | Selected QFB signatures; exact cached evidence where available |
| [source-changes.json](source-changes.json) | Seven R7-derived proof-body normalizations |
| [future-endpoints.json](future-endpoints.json) | Four mathematical contracts; implementation status and input endpoints |
| [derivation-index.json](derivation-index.json) | Four verbatim R7 mathematical derivations |
| [static-verification.json](static-verification.json) | Source, import-closure, signature and cached-evidence invariants |

`Sources/` = immutable primary-source snapshots.  
`Probes/` = canonical-import, source-only entrypoint probes.  
`QuasiFeffermanB/` = existing candidate project source graph.  
`SNAPSHOT_IMPORT_GRAPH_ADDITIONS = 0`.

## Pinned native environment

| Component | Identity |
|---|---|
| Methlib foundation | `09dfe94a1ef150e21d09df3013fbe09002ef139c` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| External compiler | Lean `4.33.0` |
| Cached compiler commit | `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| Allowed theorem axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Source parent | `17641ba02784ae108af0da5874073786d7df46ec` |

## Probe files

- [Mathlib.lean](Probes/Mathlib.lean): canonical Mathlib imports and `#check` commands.
- [Methlib.lean](Probes/Methlib.lean): canonical `SingularClosure` imports and `#check` commands.
- [QFB.lean](Probes/QFB.lean): root import; selected declarations and theorem-level axiom commands.

`PROBE_EXECUTION_STATUS = NOT_EXECUTED`.  
`EXTERNAL_ROOT_RUNNER = ../../preload.cmd`.  
`EXTERNAL_FULL_PACKAGE_RUNNER = ../../run.cmd`.  
`SOURCE_PROBE_ENTRY = ../../preload.lean`.

Source snapshots are an inspection subset. The existing package preparation
supplies the complete pinned foundation and Mathlib dependencies. The source
probes are excluded from the compiled candidate graph and introduce no proof
premises. External probe execution follows successful compilation of its imports.

## Candidate normalizations

| Source | Normalization |
|---|---|
| `CaloricFiniteNorm` | Explicit volume and finite-set arguments |
| `CaloricGalerkinBudget` | Derivative-value congruence; scalar identities; `PiLp.ext` |
| `ThetaLattice` | `Finset.product_eq_sprod` before finite product sums |
| `PhysicalFourierL2` | Exact torus-representative composition |
| `TailEnergy` | Explicit derivative columns and original-gradient translation |
| `Endpoints.FiniteTimeTest` | Typed continuity; interval inclusion; private pairing-derivative theorem |
| `Endpoints.TestProjection` | Terminal tactic normalization |

## Retained external evidence

[Cached run 43523716429](https://github.com/randogelist/Methlib/actions/runs/43523716429)
corresponds to the source parent. Its exact results are `42 PASS`, `7 FAIL`,
`25 BLOCKED_BY_DEPENDENCY`, and `227` audited declarations. Its observed
verified object-cache hits equal `34`.

R8 preserves all `42` passing dependency fingerprints and all `227` audited
declaration source hashes. Cache reuse additionally requires the exact native
pins, compiler identity and object SHA256. The external runner repeats the exact
theorem-level audit for each reused module. These retained facts do not certify
any changed R8 proof body.

## Mathematical continuation

`R7_BUFFERED_SUBCRITICAL_RESTART`  
`R7_BUFFERED_H1_RESTART_BOUND`  
`R7_QUANTITATIVE_CLASSICAL_TAIL_DISSIPATION`  
`R7_GLOBAL_CONULL_ENERGY_STARTS`

These names identify mathematical contracts. New Lean declarations under these
names have not been implemented. The fourth contract reuses the already audited
`lh_ae_good_energy_time` after the candidate Q01 existence chain.

The exact frozen threshold remains

\[
T_\star(a,\nu)=\frac{\lVert a\rVert_2^4}{8\pi^2\nu^5}.
\]

`A_TIER(new_source)` requires matching external native compilation and the exact
theorem-level axiom audit. `FORMAL_CLOSURE` and `UNCONDITIONAL_CLOSURE` remain
unestablished for the root.
