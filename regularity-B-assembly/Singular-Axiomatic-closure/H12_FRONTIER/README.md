# Singular-Axiomatic-closure

**H^(1/2)_{sigma,0,small}: !!!! UNCONDITIONAL_CLOSURE.**

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

$$
\nu>0,\quad a\in\dot H^{1/2}_{\sigma,0}(\mathbb T^3),\quad
C_*\|a\|_{\dot H^{1/2}}<\nu
\quad\Longrightarrow\quad
\mathrm{AX6}_\nu(a)\ \land\ \mathrm{GlobalRegular}_\nu(a).
$$

Domain: unit three-torus. Forcing: zero. Initial trace: strong Hhalf.
Smoothness: positive time. Constants: C_*>0, c_*=C_*^(-1).
Additional analytic, certificate, or admission premises: none.

The same constructed solution satisfies global L2(H3half), global L2(HminusHalf)
for its actual positive-time derivative, global L4(L6), the sharp quartic-gradient
budget, actual physical Leray-Hopf membership, and uniqueness against every
member of the explicitly defined physical Leray-Hopf class with the same datum.

| Verification | Result |
|---|---|
| Exact full small-data root | PASS |
| Extension modules | 104/104 |
| Extension endpoint audits | 33/33 declarations; 27 audit modules |
| Original endpoint audit | 171/171 |
| Complete package build | PASS |
| Root axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Lean | 4.33.0; external cached GitHub Actions |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Local Lean executions | 0 |

Source commit: `09dfe94a1ef150e21d09df3013fbe09002ef139c`.
External evidence: [43059293572](https://github.com/randogelist/Methlib/actions/runs/43059293572).

- [Exact root](SingularClosure/NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean)
- [A-tier theorem and verification report](NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL_A_TIER.txt)
- [Verification manifest](verification/h12-final-run.json)
- [Stage ledger](H12_SMALL_STATUS.json)
- [Native cached replay](run.cmd)

## Frozen unrestricted-data root

**11/11 — !! A_TIER; !!! CONDITIONAL_FORMAL_CLOSURE.**

```lean
SingularClosure.ax6_implies_fefferman_B_0_adjust :
  AX6Statement → Fefferman_B_0_adjust
```

The universal `AX6Statement` remains an explicit unresolved premise of this
unrestricted-data implication. The small-data theorem discharges datumwise AX6
on its stated critical ball. It does not establish universal AX6.

| # | Frozen endpoint | Status |
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

[Original endpoint ledger](ENDPOINTS.json).
Historical correction/review files record earlier source checkpoints; the
verification manifest above specifies the current small-data source and audit.

## Native Windows replay

```cmd
call run.cmd
```

Pinned Lean and Mathlib; cached dependencies preserved; full source build;
33 extension exact-type/axiom checks; original 171-declaration audit.
