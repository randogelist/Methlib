# QFA Lean endpoints

| Field | Value |
|---|---|
| Branch | `QFA` |
| Mathematical derivation | `!=B_TIER` |
| Prepared Lean source | `A_TIER_CANDIDATE` |
| Public theorem candidates | 30 |
| Analytic proposition targets without supplied proofs | 3 |
| Endpoint modules | 9 |
| External compiler and theorem-level axiom audit | `PENDING` |
| Local Lean executions | 0 |

## Folder decomposition

| Folder | Derivation location | Local indices | Exact extracted scope |
|---|---|---|---|
| [Energy](QFA/Endpoints/Energy/ProductBudget.lean) | D04.01–D04.06 | LE001–LE008 | AC envelope, exact product identity, integrability, finite product budget |
| [GoodTime](QFA/Endpoints/GoodTime/Cutoff.lean) | D05.01–D05.02 | LE009–LE013 | Strict `16*pi^2` cutoff and a.e. good-predicate preservation |
| [Agmon](QFA/Endpoints/Agmon/Scalar.lean) | D06.06–D07.01 | LE015–LE025 | Scalar fourth-power estimate, exact coefficient and positive viscosity margin |
| [Comparison](QFA/Endpoints/Comparison/RelativeEnergy.lean) | D09.03–D09.04 | LE026–LE030 | Admissible starts, integral Gronwall and common-trace comparison |
| [Composition](QFA/Endpoints/Composition/GoodTimeOfEnvelope.lean) | D04 → D05 | LE014 | Energy-envelope hypotheses imply a strict good-time witness |

## Composed scalar endpoint

$$
F(t)=M^2-2\nu\int_0^tD(r)\,dr,
\qquad
0\le E\le F,\quad D\ge0\quad\text{a.e.}
$$

$$
\nu>0,\quad
\delta>\frac{M^4}{16\pi^2\nu^5},\quad
D\in L^1(0,\delta),\quad
E\text{ a.e. measurable},\quad
G\text{ a.e.}
$$

$$
\Longrightarrow\quad
\exists s\in(0,\delta):\quad G(s)\land E(s)D(s)<4\pi^2\nu^4.
$$

Candidate declaration:
`QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope`.

The product budget is derived inside this composition. The whole-space
Leray–Hopf profile and the physical meaning of `Good` remain separate
realization obligations.

## Analytic target signatures

[Contracts.lean](QFA/Endpoints/Agmon/Contracts.lean) fixes full-volume
`L2(R^3; C^3)`, Frobenius gradient energy, Schwartz derivative witnesses,
the native Fourier normalization, genuine integrability and a.e.
representative equality.

| Index | Proposition definition | Required mathematical construction |
|---|---|---|
| LC001 | `WholeSpaceSpectralEndpoint` | AD01 and AD08; physical derivative to weighted Fourier L2 |
| LC002 | `WholeSpaceInterpolationEndpoint` | Spectral identities and Cauchy–Schwarz |
| LC003 | `WholeSpaceAgmonEndpoint` | Exact radial integral, weighted Cauchy–Schwarz and AD03 |

No proof inhabitant of these three proposition targets is supplied.

## Derivations and verification inputs

- [QUASI_FEFFERMAN_A_ENDPOINT_EXTRACTION_B_TIER.txt](QUASI_FEFFERMAN_A_ENDPOINT_EXTRACTION_B_TIER.txt): complete mathematical derivations of the extracted scalar implications and exact candidate signatures.
- [QUASI_FEFFERMAN_A_ENDPOINTS_A_TIER.txt](QUASI_FEFFERMAN_A_ENDPOINTS_A_TIER.txt): candidate status and external evidence requirements.
- [Indexed root derivation](../QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt): v1.2; 116 pinned source declarations, 45 derivation locations and point-of-use local indices.
- [endpoint-manifest.json](endpoint-manifest.json): exact theorem names, source hashes, compiler and dependency pins.
- [Audit.lean](Audit.lean): exact theorem types and theorem-level axiom reports.
- [run.cmd](run.cmd): cached external native Windows execution.

## External execution

```cmd
run.cmd
```

Compiler: `leanprover/lean4:v4.33.0`.
Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Native Windows Python 3, Git, Lean and Lake are required.

The runner retrieves native Mathlib objects with `lake exe cache get`,
preserves incremental Lake outputs, builds `QFA`, and audits the 30 exact
theorem declarations. Source/dependency identities and audit evidence are
recorded under `evidence/`. Allowed foundational axioms:
`propext`, `Classical.choice`, `Quot.sound`.

The complete physical `QUASI_FEFFERMAN_A` theorem is not a Lean declaration
in this package. Scalar endpoint audit success leaves physical root
formalization pending.
