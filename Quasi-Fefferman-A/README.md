# Quasi-Fefferman-A

| Field | Value |
|---|---|
| Goal identifier | `QUASI_FEFFERMAN_A` |
| Development branch | `QFA` |
| Specification status | `FROZEN` |
| External Lean verification | `PENDING` |

## Definitions

$$
\Omega=\mathbb R^3,\qquad \nu>0\ \text{constant},\qquad f=0.
$$

$$
L^2_\sigma(\mathbb R^3)
:=
\{a\in L^2(\mathbb R^3;\mathbb R^3):
\nabla\cdot a=0\text{ in }\mathcal D'\}.
$$

$$
T_{\mathrm{QFA}}(a,\nu)
:=
\frac{\|a\|_{L^2(\mathbb R^3)}^4}{16\pi^2\nu^5}.
$$

$\mathrm{LH}_\nu(a)$: standard unforced Leray-Hopf trajectories on
$\mathbb R^3$, with the strong energy inequality and strong initial
$L^2$ trace $a$.

## Frozen root goal

$$
\begin{gathered}
\forall\nu>0\;\forall a\in L^2_\sigma(\mathbb R^3):
\\
\mathrm{LH}_\nu(a)\neq\varnothing,
\\
\forall u\in\mathrm{LH}_\nu(a):
\qquad \lim_{t\downarrow0}\|u(t)-a\|_2=0,
\\
\forall\delta>T_{\mathrm{QFA}}(a,\nu):
\\
\exists p:\quad
(u,p)\in C^\infty([\delta,\infty)\times\mathbb R^3),
\\
\partial_tu+(u\cdot\nabla)u+\nabla p=\nu\Delta u,
\qquad \nabla\cdot u=0
\quad\text{on }[\delta,\infty)\times\mathbb R^3,
\\
\mathrm{LH}_\nu(u(\delta))
=
\{\tau\mapsto u(\delta+\tau)\}.
\end{gathered}
$$

## Scope invariants

| Component | Frozen specification |
|---|---|
| Initial admissibility | All $a\in L^2_\sigma(\mathbb R^3)$ |
| Trajectory quantifier | Every $u\in\mathrm{LH}_\nu(a)$ |
| Regularity cutoff | Every $\delta>T_{\mathrm{QFA}}(a,\nu)$ |
| Uniqueness endpoint | Fixed post-cutoff trace $u(\delta)$ |
| Original-data uniqueness | Neither assumed nor concluded |
| Actual nonuniqueness | Neither assumed nor concluded |
| Early-time regularity | $(0,T_{\mathrm{QFA}}]$ outside the guarantee |
| Cutoff optimality | Not asserted |

## Proof target

$$
\int_0^\infty
\|u(t)\|_2^2\|\nabla u(t)\|_2^2\,dt
\le \frac{\|a\|_2^4}{4\nu}.
$$

$$
\delta>T_{\mathrm{QFA}}(a,\nu)
\Longrightarrow
\exists s\in(0,\delta):
\quad
s\text{ is an admissible Leray-Hopf restart time},
\quad
\|u(s)\|_2\|\nabla u(s)\|_2<2\pi\nu^2.
$$

$$
\mathrm{GlobalStrongRestart}
+
\mathrm{WeakStrongUniqueness}
\Longrightarrow
\mathrm{QFA}.
$$

## Verification status

$$
\mathrm{GoalFrozen},
\qquad
\mathrm{ExternalCompilerPass}=\mathrm{PENDING},
\qquad
\mathrm{TheoremLevelAxiomAudit}=\mathrm{PENDING}.
$$

## B-tier derivations

| Artifact | Status |
|---|---|
| [QUASI_FEFFERMAN_A_B_TIER.txt](QUASI_FEFFERMAN_A_B_TIER.txt) | Complete composed classical derivation |
| [QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt](QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt) | Exact source entry points, derived hypothesis adapters, remaining whole-space formalization obligations |

Selected source baseline: Lean `4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

`!=B_TIER`; source inspection does not establish external compiler or
theorem-level axiom-audit evidence.
