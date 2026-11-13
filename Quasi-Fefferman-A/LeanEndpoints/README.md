# QFA Lean endpoints

| Field | Value |
|---|---|
| Branch / package version | `QFA` / `0.2.0` |
| Mathematical derivation | `!=B_TIER` |
| Prepared Lean source | `A_TIER_CANDIDATE` |
| Public theorem candidates | 71 |
| Proof-carrying linear-isometry constructions | 2 |
| Exact external axiom-audit roots | 73 |
| Analytic proposition targets without supplied proofs | 3 |
| Endpoint modules | 15 |
| External compiler and exact declaration axiom audit | `PENDING` |
| Local Lean executions | 0 |

## Folder decomposition

| Folder | Derivation location | Local indices | Exact extracted scope |
|---|---|---|---|
| [Energy](QFA/Endpoints/Energy/ProductBudget.lean) | D04.01–D04.06 | LE001–LE008 | AC envelope, exact product identity, integrability, finite product budget |
| [GoodTime](QFA/Endpoints/GoodTime/Cutoff.lean) | D05.01–D05.02 | LE009–LE013 | Strict `16*pi^2` cutoff and a.e. good-predicate preservation |
| [Agmon](QFA/Endpoints/Agmon/Scalar.lean) | D06.06–D07.01 | LE015–LE025 | Scalar fourth-power estimate, exact coefficient and positive viscosity margin |
| [Comparison](QFA/Endpoints/Comparison/RelativeEnergy.lean) | D09.03–D09.04 | LE026–LE030 | Admissible starts, integral Gronwall and common-trace comparison |
| [Representation](QFA/Endpoints/Representation/Complexification.lean) | D02.01–D02.03 | LE031–LE050 | Real/vector L2 isometries, exact energy preservation, integrable compact-real-test derivative transport |
| [Representation](QFA/Endpoints/Representation/EnergyProfile.lean) | D02.05 → D04 → D05.02 | LE051–LE059 | Full-volume spatial L2 norm profile, time integrability, derived energy budget and good time |
| [Restart](QFA/Endpoints/Restart/HilbertTrace.lean) | D05.03–D05.04 | LE060–LE072 | Restricted time translation, energy inequalities and generic strong Hilbert traces |
| [Composition](QFA/Endpoints/Composition/GoodTimeOfEnvelope.lean) | D04 → D05.02 | LE014 | Scalar energy envelope to a strict good-time witness |
| [Composition](QFA/Endpoints/Composition/GoodTimeAndTrace.lean) | D02.05 → D04 → D05.03 | LE073 | Concrete field profile to strict good time, retained energy start and both strong traces |

LE031 and LE041 construct actual `LinearIsometry` objects. Their linearity
and norm-preservation proof bodies are separate axiom-audit roots.

## Composed field endpoint

$$
H=L^2(\mathbb R^3;\mathbb R^3),\quad
E(t)=\|u(t)\|_H^2,\quad D(t)=\sum_{j=1}^{3}\|G_j(t)\|_H^2.
$$

`EnergyProfile ν a u G` retains finite-horizon a.e. strong measurability
of `u`, time `MemLp 2` for each supplied spatial L2 field `G_j`, and

$$
E(t)+2\nu\int_0^tD(r)\,dr\le\|a\|_H^2\qquad(t\ge0).
$$

Define

$$
\operatorname{EnergyStart}(s)
\iff
\forall r\ge s,\quad
E(r)+2\nu\int_s^rD(q)\,dq\le E(s).
$$

Additional premises:

$$
\nu>0,\qquad \delta>\frac{\|a\|_H^4}{16\pi^2\nu^5};
$$

$$
\forall b\in H,\quad t\mapsto\langle u(t),b\rangle
\text{ is continuous on }[0,\infty);
$$

$$
\operatorname{Good}(s)\land\operatorname{EnergyStart}(s)
\quad\text{for a.e. }s\in(0,\delta).
$$

Exact conclusion of LE073:

$$
\begin{gathered}
\exists s\in(0,\delta):\quad
\operatorname{Good}(s)\land\operatorname{EnergyStart}(s),
\\
E(s)D(s)<4\pi^2\nu^4,
\\
u(t)\xrightarrow[t\downarrow s]{H}u(s),\qquad
u(s+\tau)\xrightarrow[\tau\downarrow0]{H}u(s).
\end{gathered}
$$

Candidate declaration:
`QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace`.

The product integrability and product budget are derived from the profile.
Every upper endpoint in `EnergyStart` is retained. Negative-time values of
total-real functions remain auxiliary. The relation `G_j = ∂_j u`, the
initial-trace identification of `a`, divergence, the weak momentum equation,
and actual Leray–Hopf membership require their physical constructions.

## Representation and analytic boundaries

[Complexification.lean](QFA/Endpoints/Representation/Complexification.lean)
constructs the componentwise real linear isometry and its full-volume L2
lift. It preserves supplied velocity, Frobenius gradient, and Laplacian
energies exactly. A supplied real compact-test weak derivative is
transported after both test products have been proved integrable.

The AD08 extension to complex/Schwartz tests and tempered derivatives,
physical derivative identification, and actual Laplacian assembly remain
separate formalization obligations. The generic Restart modules do not
contain the physical weak-equation restart proof at D05.05.

[Contracts.lean](QFA/Endpoints/Agmon/Contracts.lean) fixes the full-volume
complex carrier, native Fourier normalization and actual analytic targets.

| Index | Proposition definition | Required mathematical construction |
|---|---|---|
| LC001 | `WholeSpaceSpectralEndpoint` | Physical derivative realization and AD08; exact weighted Fourier L2 identities |
| LC002 | `WholeSpaceInterpolationEndpoint` | Spectral identities and Cauchy–Schwarz |
| LC003 | `WholeSpaceAgmonEndpoint` | Exact radial integral, weighted Cauchy–Schwarz and AD03 |

No proof inhabitant of these three proposition targets is supplied.

## Derivations and verification inputs

- [QUASI_FEFFERMAN_A_ENDPOINT_EXTRACTION_B_TIER.txt](QUASI_FEFFERMAN_A_ENDPOINT_EXTRACTION_B_TIER.txt): complete scalar derivations, LE001–LE030.
- [QUASI_FEFFERMAN_A_REPRESENTATION_RESTART_B_TIER.txt](QUASI_FEFFERMAN_A_REPRESENTATION_RESTART_B_TIER.txt): complete representation/profile/restart derivations, LE031–LE073.
- [Indexed root derivation](../QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt): v1.3; 133 pinned source declarations, 45 derivation locations, 171 source applications, and all local indices at their points of use.
- [QUASI_FEFFERMAN_A_ENDPOINTS_A_TIER.txt](QUASI_FEFFERMAN_A_ENDPOINTS_A_TIER.txt): candidate status and external evidence requirements.
- [endpoint-manifest.json](endpoint-manifest.json): exact declaration names, kinds, signatures, source hashes, and dependency pins.
- [Audit.lean](Audit.lean): compiler types and transitive axiom reports for all 73 exact declarations.
- [run.cmd](run.cmd): cached external native Windows execution.

## External execution

```cmd
run.cmd
```

Compiler: `leanprover/lean4:v4.33.0`.
Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Native Windows Python 3, Git, Lean and Lake are required.

The runner retrieves native Mathlib objects with `lake exe cache get`,
preserves incremental Lake outputs, builds `QFA`, and audits the 71 theorem
declarations and two proof-carrying constructions. Source and dependency
identities and audit evidence are recorded under `evidence/`. Allowed
foundational axioms: `propext`, `Classical.choice`, `Quot.sound`.

The complete physical `QUASI_FEFFERMAN_A` theorem is not a Lean declaration
in this package. Individual endpoint audit success leaves physical root
formalization pending.
