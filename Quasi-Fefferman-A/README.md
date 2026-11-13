# Quasi-Fefferman-A

| Field | Value |
|---|---|
| Goal identifier | `QUASI_FEFFERMAN_A` |
| Development branch | `QFA` |
| Specification status | `FROZEN` |
| External endpoint verification | `PASS`; LE001–LE093 |
| Physical root formalization | `B_TIER_ROOT_FORMALIZATION_PENDING` |

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
\mathrm{EndpointCompilerPass}=\mathrm{PASS},
\qquad
\mathrm{EndpointAxiomAudit}=\mathrm{PASS}.
$$

Exact scope: LE001–LE093, compiled commit `97d745678734a2bb9d7c1d9d4ae05d1a36c0a162`.
[CI run 43528295686](https://github.com/randogelist/Methlib/actions/runs/43528295686), attempt 1; [verified evidence](CI/97d745678734a2bb9d7c1d9d4ae05d1a36c0a162/VERIFICATION.txt).
The complete physical root remains `B_TIER`. The endpoint ledger records
current status; preserved source comments record their preparation snapshot.

## B-tier derivations

| Artifact | Status |
|---|---|
| [QUASI_FEFFERMAN_A_B_TIER.txt](QUASI_FEFFERMAN_A_B_TIER.txt) | Complete composed classical derivation |
| [QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt](QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt) | v1.4: 139 pinned source declarations at 45 derivation locations; 180 source applications; LE001–LE093 and four analytic targets indexed at their points of use |
| [QUASI_FEFFERMAN_A_ENDPOINT_EXTRACTION_B_TIER.txt](LeanEndpoints/QUASI_FEFFERMAN_A_ENDPOINT_EXTRACTION_B_TIER.txt) | Complete scalar derivations, LE001–LE030 |
| [QUASI_FEFFERMAN_A_REPRESENTATION_RESTART_B_TIER.txt](LeanEndpoints/QUASI_FEFFERMAN_A_REPRESENTATION_RESTART_B_TIER.txt) | Complete representation, field-profile, time-translation and strong-trace derivations, LE031–LE073 |
| [QUASI_FEFFERMAN_A_ASSEMBLY_B_TIER.txt](LeanEndpoints/QUASI_FEFFERMAN_A_ASSEMBLY_B_TIER.txt) | Complete reusable representation/restart/analytic/comparison assemblies, LE074–LE093 |

Selected source baseline: Lean `4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

`!=B_TIER`; source inspection does not establish external compiler or
theorem-level axiom-audit evidence.

## Folderwise Lean endpoint extraction

[LeanEndpoints](LeanEndpoints/README.md), version `0.3.0`:
`Energy`, `GoodTime`, `Agmon`, `Comparison`, `Representation`, `Restart`,
`Composition` under `LeanEndpoints/QFA/Endpoints/`.

Status: `!!=A_TIER`; 91 theorem bodies and two proof-carrying
linear-isometry constructions in 19 proof modules. Four analytic
Prop targets retain no supplied proof inhabitants. All 93 proof-bearing
declarations have matching external compiler and exact axiom-audit PASS evidence.

LE073 composes the concrete full-volume L2 energy profile, weak pairing
continuity and a.e. energy starts into a strict subcritical time, the
retained energy-start inequality and strong right/shifted traces.
Actual weak-gradient realization and the translated weak momentum equation
remain separate physical formalization obligations. The QFA root statement
and its strict regularity cutoff remain frozen.

[run.cmd](LeanEndpoints/run.cmd): cached external native Windows Lean
4.33.0 execution and exact declaration-level axiom auditing. Local Lean
executions: zero.

## Reusable assembly import

```lean
import QFA.Assembly
```

[Assembly](LeanEndpoints/QFA/Assembly/README.md): four interfaces under
`LeanEndpoints/QFA/Assembly/`, with 20 verified assembly theorems.
The assembly constructs shifted energy data, composes supplied analytic
estimates, constructs comparison sequences, and restricts singleton equality
to nonnegative time. [assembly-manifest.json](LeanEndpoints/assembly-manifest.json)
records the subsequent physical stages and named unresolved analytic inputs.
