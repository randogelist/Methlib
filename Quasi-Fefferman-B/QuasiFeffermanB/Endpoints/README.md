# Quasi-Fefferman-B: R6 endpoint preload

| Field | Value |
|---|---|
| Mathematical derivation | `B_TIER`; complete R1–R5 derivation in `QUASI_FEFFERMAN_B_METHLIB_COMPOSED_COMPLETION_B_TIER.txt` |
| New Lean source | `A_TIER_CANDIDATE` |
| Exact root | `QuasiFeffermanB.QuasiFeffermanBStatement` |
| Root declaration | `QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED` |
| External compilation of this extraction | Pending |
| Theorem-level axiom audit of this extraction | Pending |
| Local Lean execution | `0` |
| New external Lean runs | `0` |

## R6 preload

```lean
import QuasiFeffermanB.Endpoints.Root
```

`SOURCE_PROBE = ../../preload.lean`  
`EXTERNAL_WINDOWS_ENTRY = ../../preload.cmd`  
`SOURCE_THEOREM_CHANGES = 0`  
`MANIFEST_VALIDATION = ALL_79_SOURCES`  
`ROOT_IMPORT_CLOSURE = 74_MODULES`  
`ROOT_DECLARATION_AUDITS = 409`  
`PLAN = preload-plan.json`

Cached objects require matching native pins, compiler version, transitive
source fingerprints and object SHA256. Every reused theorem module receives
a fresh exact declaration/type/axiom audit. Source preload alone establishes
no A-tier promotion. The preceding status table records the R5 assembly
before external preload execution.

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

Additional helper declarations implement physical representative transport,
finite test calculus, bounded weak convergence and the limit passages.
`endpoint-index.json` records exact file hashes, declarations, dependencies
and a topological module order.

## R5 support-interface repairs

| Source | Selected normalization |
|---|---|
| `CaloricConvolution` | Typed derivative identities; `HasDerivAt.congr_deriv`; exponential-product algebra |
| `ThetaLattice` | Exact three-coordinate square; exponential factorization; finite product sums |
| `CaloricFrequencyGeometry` | Complex scalar commutativity in the normalized inner product |
| `EnergyGlobalLimit` | Explicit coefficient transport; subtype function composition; integer Sobolev order |
| `LHRestart` | Explicit translated interval inequalities |
| `PhysicalFourierL2` | Exact torus subtype; Euclidean norm square; `integral_sub'`; zero weighted coefficient |
| `EnergyPeriodicRepresentative` | Three `memLp_congr_ae` transports; explicit `SingularClosure.gradient` |
| `EnergyGlobalPhysical` | Direct canonical-state membership transport; reduced import |
| `EnergyFiniteWeakPairing` | Native finite-pairing imports; explicit gradient |
| `EnergyPhysicalContinuity` | Direct `CriticalWeakGradient` pairing identity |

The ten support-module edits preserve 111 declaration interfaces, with one
explicit namespace qualification of the intended gradient. The nine R4 Lean
endpoint files retain their exact source bytes.

The actual root support closure decreases from 67 to 65 baseline modules;
the Q01 support closure contains 22 baseline modules. Recursive manifest
and audit discovery registers all 79 source files, 76 theorem-containing
modules and 423 theorem declarations, including the exact root declaration.
These registration counts are not compiler or audit passes.

## Deterministic root composition

```lean
import QuasiFeffermanB.Endpoints.Root

#check QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
#print axioms QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
```

Root body: `Quasi_Fefferman_B_of_LH_existence Q01_LERAY_HOPF_EXISTENCE`.

The original root retains universal physical Leray–Hopf existence, the
conclusion for every original Leray–Hopf path, the same weak gradient,
tail energy equality, trace uniqueness, and the frozen thresholds

\[
T_\star(a,\nu)=\frac{\lVert a\rVert_2^4}{8\pi^2\nu^5},
\qquad T_{\mathrm{safe}}=2T_\star,
\qquad \delta>T_\star.
\]

The explicit supplementary caloric estimate is

\[
\int_0^T\chi_{0,N}(g(t))^2\,dt
\le \frac{\lVert b\rVert_{\dot H^{1/2}}^2}{\pi\nu},
\quad
\lVert b\rVert_{\dot H^{1/2}}^2<2\pi\nu^2.
\]

Its exact library type is the squared norm of
`criticalSobolevLower 1 2 (by norm_num) b`; the source signature controls
the normalization.

## Source and cached evidence

| Input | Exact identity |
|---|---|
| QFB baseline | `e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c` |
| Methlib foundation | `09dfe94a1ef150e21d09df3013fbe09002ef139c` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Existing cached external run | `43151440082` |
| Cached compiler | Lean `4.33.0`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| Cached exact declaration passes | `178`, baseline declarations only |
| Cached baseline module results | `34 PASS`; `8 FAIL`; `28 BLOCKED_BY_DEPENDENCY` |
| Allowed audit axioms | `propext`, `Classical.choice`, `Quot.sound` |

The six inherited direct failures have candidate source repairs. Their
external compilation and all dependent declaration audits remain pending.
The three R3 import reductions are applied. The 34 previously passing module
dependency fingerprints and 178 audited declaration source hashes still
match; the changed modules and extracted endpoints acquire no new pass.

Placement: this folder is an overlay within the existing QFB package.
Foundation and Mathlib dependencies are supplied by that package.
No standalone dependency installation or compilation is performed here.

Promotion predicate:

```text
A_TIER(new_declaration) :=
  matching_external_compiler_success
  AND exact_source_and_dependency_identity
  AND theorem_level_axiom_audit
  AND axioms ⊆ {propext, Classical.choice, Quot.sound}.

FORMAL_ROOT_STATUS = PENDING.
UNCONDITIONAL_CLOSURE = NOT_ESTABLISHED_BY_THIS_EXTRACTION.
```
