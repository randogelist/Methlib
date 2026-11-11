# Singular-Axiomatic-closure

**11/11 — !! A_TIER. !!! CONDITIONAL_FORMAL_CLOSURE.**

```lean
SingularClosure.ax6_implies_fefferman_B_0_adjust :
  AX6Statement → Fefferman_B_0_adjust
```

`AX6Statement`: unresolved analytic premise. Custom axiom declarations: none.

| Verification | Result |
|---|---|
| Root compiler | PASS |
| Root exact type | PASS |
| Root axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Complete source build | PASS |
| Aggregate 171-declaration audit | Pending syntax-repair verification |
| Lean | 4.33.0, external cached GitHub Actions |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Local Lean executions | 0 |
| Unconditional closure | Not established |

Root evidence: [353038e0 / run 42960942482](https://github.com/randogelist/Methlib/actions/runs/42960942482).

## Exact scope

$$
\mathrm{AX6Statement}\Rightarrow\forall\nu>0\ \forall a\in C^\infty_{\sigma,0}(\mathbb T^3),
\ \exists(u,p)\ \mathrm{GlobalSmoothNSE}_\nu(a,u,p).
$$

`GlobalSmoothNSE`: joint smoothness on closed forward spacetime; spatial periodicity; divergence-free velocity; actual pointwise unforced NSE; initial trace `u(0)=a`; zero velocity and pressure means. Time differentiation at zero: `derivWithin` on `[0,∞)`. Smallness premises: none.

## Unresolved premise

$$
\forall\nu>0\ \forall a\in C^\infty_{\sigma,0}\ \forall T>0\ \exists M<\infty\ \forall N\ge1\ \forall g_N:
\quad\int_0^T\left(\sum_{A=1}^{6}\|\nabla Q_Au_N(t)\|_2^2\right)^2dt\le M.
$$

`g_N : GalerkinSolution ν a N`; `M` is independent of `N` and `g_N`. Spatial and temporal budget integrals: nonnegative extended integrals.

## Frozen endpoints

| # | Endpoint | Status |
|---:|---|---|
| 1 | `SIX_CHANNEL_PROJECTIONS` | !! A_TIER |
| 2 | `SIX_CHANNEL_ENSTROPHY_EQ` | !! A_TIER |
| 3 | `GALERKIN_GLOBAL_EXISTS_UNIQUE` | !! A_TIER |
| 4 | `GALERKIN_ENERGY_IDENTITY` | !! A_TIER |
| 5 | `GALERKIN_ENSTROPHY_INEQUALITY` | !! A_TIER |
| 6 | `CUBIC_ENERGY_OF_SQUARE_BUDGET` | !! A_TIER |
| 7 | `AX6_UNIFORM_STRONG_BOUNDS` | !! A_TIER |
| 8 | `GALERKIN_GLOBAL_STRONG_LIMIT` | !! A_TIER |
| 9 | `GLOBAL_STRONG_SMOOTH_BOOTSTRAP` | !! A_TIER |
| 10 | `PERIODIC_PRESSURE_RECOVERY` | !! A_TIER |
| 11 | `ax6_implies_fefferman_B_0_adjust` | !! A_TIER |

## Artifacts

- [Root.lean](SingularClosure/Root.lean)
- [Root A-tier report](ax6_implies_fefferman_B_0_adjust_A_TIER.txt)
- [Complete closure report](Singular_Axiomatic_Closure_A_TIER.txt)
- [run.cmd](run.cmd)
- [Endpoint ledger](ENDPOINTS.json)
- [Compiler, exact-type and axiom evidence](verification/)

Native Windows replay, from the extracted project directory:

```cmd
call run.cmd
```

`run.cmd`: pinned toolchain, pinned Mathlib cached objects, full build, fresh 171-declaration audit.
