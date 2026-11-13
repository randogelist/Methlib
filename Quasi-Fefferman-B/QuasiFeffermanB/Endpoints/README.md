# Quasi-Fefferman-B endpoints: R8

| Field | Value |
|---|---|
| Source status | `A_TIER_CANDIDATE` |
| Mathematical derivation | `R7`; `!=B_TIER` |
| Exact root | `QuasiFeffermanB.QuasiFeffermanBStatement` |
| Root declaration | `QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED` |
| Public statement changes in R8 | `0` |
| Candidate proof-source changes | `7` modules |
| Local Lean / new external runs / new promotions | `0 / 0 / 0` |

## Module–endpoint map

| Module | Selected export |
|---|---|
| `InitialCoefficients` | `ENERGY_GALERKIN_LIMIT_INITIAL_COEFFICIENTS` |
| `FiniteTimeTest` | `ENERGY_GALERKIN_PAIRING_HASDERIV`; `ENERGY_GALERKIN_TIME_TEST_IDENTITY` |
| `TestProjection` | `ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM` |
| `WeakH0Limit` | `ENERGY_H0_WEAK_TENDSTO` |
| `PhysicalMomentum` | `ENERGY_GALERKIN_PHYSICAL_MOMENTUM` |
| `LimitEnergy` | `ENERGY_PERIODIC_LIMIT_ENERGY` |
| `LerayHopfExistence` | `Q01_LERAY_HOPF_EXISTENCE` |
| `CaloricBudget` | `SPECTRAL_H1_CALORIC_BUDGET_EXPLICIT` |
| `Root` | `QUASI_FEFFERMAN_B_COMPOSED` |

## Source and cache entrypoints

[endpoint-index.json](endpoint-index.json) contains source hashes, exact selected
signatures, cached status, import topology and R5/R6 provenance.
[preload-plan.json](preload-plan.json) fixes the R8 root import closure:
`74` modules, `71` theorem-audit modules, `409` registered declarations.
The full source manifest retains `79` files, `76` theorem-containing modules and
`423` public theorem registrations.

[SourcePreload/R8](../../SourcePreload/R8/README.md) supplies `35` pinned Lean source
snapshots, the source API registry, three unexecuted probes, and the four R7
mathematical continuation contracts. Snapshot files remain outside the compiled
candidate graph.

[Cached run 43523716429](https://github.com/randogelist/Methlib/actions/runs/43523716429):
`42 PASS`, `7 FAIL`, `25 BLOCKED_BY_DEPENDENCY`, `227` exact audited declarations.
The seven failed modules now contain candidate proof-body normalizations. All
`42` previous PASS dependency fingerprints and `227` declaration source hashes
are preserved. Existing audit facts retain their exact source premises.

## Deterministic root

```lean
import QuasiFeffermanB.Endpoints.Root

#check QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
#print axioms QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
```

`ROOT_BODY = Quasi_Fefferman_B_of_LH_existence Q01_LERAY_HOPF_EXISTENCE`.

\[
T_\star(a,\nu)=\frac{\lVert a\rVert_2^4}{8\pi^2\nu^5},
\qquad T_{\mathrm{safe}}=2T_\star,
\qquad \delta>T_\star.
\]

The original physical velocity, weak gradient, tail energy equality, every-trace
future uniqueness, and all root quantifiers are preserved.

## External gate

`EXTERNAL_WINDOWS_ENTRY = ../../preload.cmd`  
`COMPILER = Lean 4.33.0`  
`CACHE_IDENTITY = native pins + compiler + transitive fingerprint + object SHA256`  
`FRESH_AUDIT = every selected registered declaration, including reused modules`  
`ALLOWED_AXIOMS = {propext, Classical.choice, Quot.sound}`  
`FORMAL_ROOT_STATUS = PENDING`.
