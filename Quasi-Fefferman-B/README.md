# Quasi-Fefferman_B

| Field | Value |
|---|---|
| Mode | `B_TIER_DERIVATION` |
| Round | `1` |
| Canonical theorem | `Quasi_Fefferman_B` |
| Root status | `! B_TIER` |
| Branch | `QUASI-FEFFERMAN-B` |
| Repository directory | `/Quasi-Fefferman-B/` |
| New Lean root | `PENDING` |
| Local Lean executions | `0` |

[QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt](QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt)

## Frozen statement

$$
\mathbb T^3=(\mathbb R/\mathbb Z)^3,\qquad \nu>0,\qquad f=0,
\qquad E=L^2_{\sigma,0}(\mathbb T^3;\mathbb R^3).
$$

$$
T_*(a,\nu)=\frac{\|a\|_2^4}{8\pi^2\nu^5}.
$$

$$
\forall a\in E:\quad \mathrm{LH}_\nu(a)\ne\varnothing,
\qquad
\forall u\in\mathrm{LH}_\nu(a),\ \forall\delta>T_*(a,\nu):
\quad (u,p)\in C^\infty([\delta,\infty)\times\mathbb T^3).
$$

$$
\forall t\ge\delta:\quad
\|u(t)\|_2^2+2\nu\int_\delta^t\|\nabla u(s)\|_2^2\,ds
=\|u(\delta)\|_2^2,
\qquad
\mathrm{LH}_\nu(u(\delta))=\{r\mapsto u(\delta+r)\}.
$$

`sigma` = distributional divergence zero; `0` = spatial mean zero.
`LH` = standard Leray–Hopf trajectories, including strong initial trace.
Smoothness = existence of smooth representatives; pressure = zero-mean gauge.
Velocity equality = equality of the weakly continuous L² trajectories.
Initial-history uniqueness and arbitrary positive cutoffs are outside scope.

## Reuse baseline

| Object | Pinned evidence |
|---|---|
| Source revision | `09dfe94a1ef150e21d09df3013fbe09002ef139c` |
| Imported foundation | `regularity-B-assembly/Singular-Axiomatic-closure` |
| Compiler | external Lean `4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Base audit | 204 matching exact-type/axiom reports |
| Branch/tree inventory | 28 repositories; 172 pre-existing branch tips |

[Pinned foundation](https://github.com/randogelist/Methlib/tree/09dfe94a1ef150e21d09df3013fbe09002ef139c/regularity-B-assembly/Singular-Axiomatic-closure)
· [Cached external evidence](https://github.com/randogelist/Methlib/actions/runs/43059293572)

Existing verified admission:

$$
C_{\mathrm{NL}}\|b\|_{\dot H^{1/2}}<\nu
\Longrightarrow \operatorname{Reg}_\nu(b).
$$

Required numerical admission:

$$
\|b\|_{\dot H^{1/2}}^2<2\pi\nu^2
\Longrightarrow \operatorname{Reg}_\nu(b).
$$

`C_NL` has no verified numerical upper bound in the selected foundation.
The second implication remains a new formal endpoint; its mathematical
caloric/theta–Schur derivation is included in the TXT.

## Endpoint plan

| Endpoints | Contract |
|---|---|
| Q00–Q03 | Physical semantics; arbitrary-L² LH existence; energy; midpoint interpolation |
| Q04–Q05 | Measurable critical-time budget; conull restart with strong right trace |
| Q06; A01–A11 | Exact numerical admission through caloric and theta–Schur estimates |
| Q07–Q10 | Strict good-time selection; same-trajectory identification; smooth tail and pressure |
| Q11–Q14 | Energy equality; trace uniqueness; zero case; deterministic root assembly |

`ROOT_A_TIER = PENDING_EXTERNAL_COMPILER_AND_THEOREM_AXIOM_AUDIT`.

Subsequent formalization: pinned-cache reuse; independent endpoint bodies;
native asynchronous elaboration where dependency-safe; deterministic root.
All source, semantic, analytic, admission, and audit obligations remain
explicit until discharged. No local Lean execution.
