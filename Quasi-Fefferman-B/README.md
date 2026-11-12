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
| Implementation | External cached compilation in progress |
| Endpoint resolution marker | `!=!` only after matching external compiler and axiom audit |
| Local Lean executions | `0` |

[QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt](QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt)

## External endpoint status

`LOCAL_LEAN_EXECUTIONS = 0`.

`!=!` = the exact named endpoint passed the external compiler and its
matching theorem-level axiom audit; permitted axioms:
`propext`, `Classical.choice`, `Quot.sound`.

`endpoint-manifest.json` pins candidate source hashes and audited names.
The external evidence artifact records compiler-emitted types and axiom lists.
Passing intermediate implications retain every displayed premise; they do
not automatically resolve the larger Q/A endpoint.

| Endpoints | Initial implementation status |
|---|---|
| Q00 | Concrete physical carrier and exact root contract defined |
| Q01 | Energy-level Fourier compactness candidates; actual LH limit pending |
| Q02 | Native LH energy theorem candidate |
| Q03–Q04 | Physical midpoint interpolation and trajectory-budget candidates |
| Q05 | Native full LH restart candidate |
| Q06 | Exact numerical caloric admission pending |
| Q07 | Native strict good-time theorem candidate |
| Q08–Q10 | Actual comparison, smoothing, and pressure adapters in progress |
| Q11–Q12 | Tail energy and unique future assembly pending |
| Q13 | Scalar cutoff and zero-LH smooth-representative candidates |
| Q14 | Concrete root contract fixed; root proof pending |
| A01–A11 | Independent caloric lemmas in progress; full admission pending |

[External compiler workflow](../.github/workflows/quasi-fefferman-b.yml)
· [Candidate manifest](endpoint-manifest.json)
· [Native Windows runner](run.cmd)

## Verified exact declarations

Evidence: [external run 43147241136](https://github.com/randogelist/Methlib/actions/runs/43147241136),
commit `09def662a6ee3a7b8bb2c3b20c82eeaa5292b13d`.

[Source-hash and axiom ledger](evidence/run-43147241136-reinspection.json).
The initial workflow parser rejected standard axioms with printed universe
arguments; direct cached-log reinspection verified the same three permitted
axiom constants. The parser and rejection fixtures are corrected.

| Marker | Exact declaration |
|---|---|
| `!=!` | `POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN` |
| `!=!` | `TWO_LH_EQUAL_OF_POSITIVE_FLOW_TRACE_AND_SERRIN` |
| `!=!` | `CONTINUOUS_QUADRATIC_BARRIER` |
| `!=!` | `QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET` |
| `!=!` | `QUADRATIC_BARRIER_ZERO_HEAT_BUDGET` |
| `!=!` | `QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET` |
| `!=!` | `QUADRATIC_BARRIER_SQUARE_BUDGET` |
| `!=!` | `GALERKIN_H2_SEED_OF_ENSTROPHY_ACCUMULATION` |
| `!=!` | `GALERKIN_POSITIVE_FLOW_OF_H2_SEED` |

These declarations retain their explicit quantitative/analytic premises.
`QFB_ROOT_UNCONDITIONAL_A_TIER = PENDING`.

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

## Concrete implication chain

$
M:=\|a\|_2,\qquad
L(v):=\|v\|_2^2,\qquad
D(v):=\|\nabla v\|_2^2,\qquad
H(v):=\sum_{k\ne0}2\pi|k|\,|\widehat v(k)|^2.
$

$
H(v)=\|v\|_{\dot H^{1/2}}^2
\quad(v\in H^{1/2}_{\sigma,0}),\qquad
H:L^2_{\sigma,0}\longrightarrow[0,\infty].
$

### Q00–Q02: actual existence and energy

$
a\in E
\Longrightarrow
\mathrm{LH}_\nu(a)\ne\varnothing.
$

$
\forall u\in\mathrm{LH}_\nu(a),\ \forall\delta>0,\ \forall t\ge0:
\quad
L(u(t))\le M^2,\qquad
\int_0^\delta D(u(t))\,dt\le\frac{M^2}{2\nu}.
$

### Q03–Q04: Fourier interpolation and time budget

$
\begin{aligned}
H(v)
&=\sum_{k\ne0}|\widehat v(k)|\,
                 \bigl(2\pi|k|\,|\widehat v(k)|\bigr)\\
&\le
\left(\sum_{k\ne0}|\widehat v(k)|^2\right)^{1/2}
\left(\sum_{k\ne0}4\pi^2|k|^2|\widehat v(k)|^2\right)^{1/2}.
\end{aligned}
$

$
v\in H^1_{\sigma,0}
\Longrightarrow
H(v)^2\le L(v)D(v).
$

$
\boxed{
\int_0^\delta H(u(t))^2\,dt
\le M^2\int_0^\delta D(u(t))\,dt
\le\frac{M^4}{2\nu}.}
$

Measurability: nonnegative finite Fourier sums → monotone extended sum.

### Q05: admissible restart times

$
\exists R_u\subset(0,\infty):
\quad |(0,\infty)\setminus R_u|=0,
$

$
s\in R_u
\Longrightarrow
\begin{cases}
u(s)\in H^1_{\sigma,0},\\
\operatorname{Shift}_s u\in\mathrm{LH}_\nu(u(s)),\\
\displaystyle\lim_{r\downarrow0}
\|u(s+r)-u(s)\|_2=0.
\end{cases}
$

$
(\operatorname{Shift}_s u)(r):=u(s+r).
$

Construction: countable intersection of compatible energy-start sets and
H¹-trace sets; weak continuity + the energy inequality at s → strong right trace.

### Q07: strict good-time selection

$
\delta>T_*(a,\nu)=\frac{M^4}{8\pi^2\nu^5}
\Longrightarrow
\exists s\in R_u\cap(0,\delta):
H(u(s))<2\pi\nu^2.
$

Integral contradiction:

$
H(u(t))\ge2\pi\nu^2\ \text{a.e. on }(0,\delta)
\Longrightarrow
4\pi^2\nu^4\delta
\le\int_0^\delta H(u(t))^2\,dt
\le\frac{M^4}{2\nu},
$

$
\Longrightarrow\quad
\delta\le T_*(a,\nu)\quad\bot.
$

### Q06, A01–A11: exact admission of the selected trace

$
b:=u(s),\qquad
Q(b):=
\left[
\int_0^\infty
\left(\sum_{k\ne0}|\widehat b(k)|e^{-4\pi^2|k|^2t}\right)^2dt
\right]^{1/2}.
$

$
\boxed{
H(b)<2\pi\nu^2
\Longrightarrow
Q(b)^2\le\frac{H(b)}{4\pi}<\frac{\nu^2}{2}
\Longrightarrow
Q(b)<\frac{\nu}{\sqrt2}
\Longrightarrow
\operatorname{Reg}_\nu(b).}
$

$
\operatorname{Reg}_\nu(b):=
\exists(v,p_b):
\quad
\mathrm{LH}_\nu(b)=\{v\},\quad
\lim_{t\downarrow0}\|v(t)-b\|_2=0,\quad
(v,p_b)\in C^\infty((0,\infty)\times\mathbb T^3),
$

with the LH energy equality and zero-mean pressure gauge.

Schur subchain:

$
\Theta(t):=\sum_{k\in\mathbb Z^3}e^{-t|k|^2},\qquad
\Theta(t)-1\le(\pi/t)^{3/2}
$

$
\Longrightarrow\
\sum_{\ell\ne0}
\frac1{|\ell|^2(r^2+|\ell|^2)}
\le\frac{2\pi^2}{r}
\Longrightarrow\
Q(b)^2\le\frac{H(b)}{4\pi}.
$

Caloric subchain:

$
\chi_0(v):=\sum_{k\ne0}|\widehat v(k)|,\qquad
Y:=L^2((0,\infty);\ell^1),\qquad
\beta_\nu:=\frac1{2\sqrt{2\nu}},\qquad
h:=\frac{Q(b)}{\sqrt\nu}.
$

$
B_\nu(v,w)(t):=
-\frac12\int_0^t e^{\nu(t-r)\Delta}
\mathbb P\nabla\!\cdot(v\otimes w+w\otimes v)(r)\,dr.
$

$
\|B_\nu(v,w)\|_Y\le\beta_\nu\|v\|_Y\|w\|_Y,\qquad
\|e^{\nu t\Delta}b\|_Y=h.
$

$
Q(b)<\frac{\nu}{\sqrt2}
\Longrightarrow
4\beta_\nu h<1
\Longrightarrow
\sup_N\int_0^\infty\chi_0(u_N(t))^2\,dt
\le S:=\frac{4Q(b)^2}{\nu}.
$

$
\frac{d}{dt}\|\nabla u_N\|_2^2+\nu\|\Delta u_N\|_2^2
\le\nu^{-1}\chi_0(u_N)^2\|\nabla u_N\|_2^2
$

$
\Longrightarrow\
\|\nabla u_N(t)\|_2^2
\le\frac{\|b\|_2^2e^{S/\nu}}{2\nu t}
\Longrightarrow\
\operatorname{Reg}_\nu(b).
$

Final analytic composition:
Galerkin compactness + retained caloric budget + positive-time H¹/H²
bounds + parabolic smoothing + all-LH relative-energy comparison.

### Q08–Q10: identification of the original trajectory

$
\mathrm{LH}_\nu(b)=\{v\},\qquad
\operatorname{Shift}_s u\in\mathrm{LH}_\nu(b)
\Longrightarrow
\operatorname{Shift}_s u=v.
$

$
s<\delta,\quad
(v,p_b)\in C^\infty((0,\infty)\times\mathbb T^3)
\Longrightarrow
\boxed{(u,p)\in C^\infty([\delta,\infty)\times\mathbb T^3).}
$

$
-\Delta p=\sum_{i,j}\partial_i\partial_j(u_i u_j),\qquad
\int_{\mathbb T^3}p(t,x)\,dx=0.
$

### Q11–Q14: energy, trace uniqueness, and root

$
\forall t\ge\delta:
\quad
L(u(t))+2\nu\int_\delta^tD(u(r))\,dr=L(u(\delta)).
$

$
\mathrm{LH}_\nu(u(\delta))
=\{\operatorname{Shift}_\delta u\}.
$

$
a\ne0\Longrightarrow2T_*(a,\nu)>T_*(a,\nu),\qquad
a=0\Longrightarrow(u,p)=(0,0).
$

$
\boxed{
\mathrm{Q01}+\mathrm{Q09}+\mathrm{Q10}+
\mathrm{Q11}+\mathrm{Q12}+\mathrm{Q13}
\Longrightarrow
\mathrm{Q14}=\texttt{Quasi\_Fefferman\_B}.}
$

Full derivations and exact endpoint signatures:
[TXT §§2–3, §6, Appendix A](QUASI_FEFFERMAN_B_CHAIN_R1_B_TIER.txt).

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

## Concrete reuse map

Base namespace: SingularClosure.
Evidence scope: exact existing declaration types at the pinned source;
new adapters and new root remain uncompiled.

| Existing endpoint | Concrete role | Remaining formal obligation |
|---|---|---|
| CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE; GALERKIN_ENERGY_IDENTITY | Q01 approximants and A06 finite energy | Arbitrary-L² infinite-dimensional LH limit |
| FINITE_PHYSICAL_ENERGY_PARSEVAL; FINITE_PHYSICAL_ENSTROPHY_PARSEVAL | Q03 Fourier/physical normalization | Infinite H¹ midpoint interpolation |
| CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON | Q08/Q12 relative-energy comparison | Compatible regular reference and translated LH semantics |
| INFINITE_TRANSPORT_PRESSURE_RECOVERY; SOBOLEV_TRANSPORT_PRESSURE_JOINT_SMOOTH | Q10 pressure recovery | Compatible positive-time Sobolev flow |
| NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL | Verified C-small actual-PDE baseline | Exact numerical admission Q06 |
| NSE.squaredNormInterpolation; NSE.fourthPowerIntegrable; NSE.integratedSerrinBound (stokes-conditional) | Q04 scalar integral algebra | Actual measurable Fourier profile and physical interpolation |

Reuse source/evidence URLs and exact premises: TXT Appendices B–E.
An existing theorem's hypotheses remain required after import.
The standard-only axiom audit does not discharge a quantified analytic premise.

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
