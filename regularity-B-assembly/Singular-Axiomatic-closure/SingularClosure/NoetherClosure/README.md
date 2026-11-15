# NOETHER_CLOSURE — Methlib extension (candidate)

Status: A_TIER_CANDIDATE only. No matching external compiler or theorem-level audit has passed for these new sources.

## Existing architecture
- `SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE`: global finite ODE (existing)
- `SingularClosure.GALERKIN_ENERGY_IDENTITY`: finite NSE energy (existing)
- `SingularClosure.SIX_CHANNEL_FINITE_ENSTROPHY_EQ`: exact physical six-channel identity (existing)
- `SingularClosure.SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ`: exact square-budget identity (existing)
- `SingularClosure.AX6_UNIFORM_STRONG_BOUNDS`: AX6 → H1/H2/derivative control (existing conditional)
- `SingularClosure.GALERKIN_GLOBAL_STRONG_LIMIT`: AX6 → all-order strong-limit construction (existing conditional)
- `SingularClosure.GLOBAL_STRONG_SMOOTH_BOOTSTRAP` / `PERIODIC_PRESSURE_RECOVERY` (existing)
- `SingularClosure.ax6_implies_fefferman_B_0_adjust`: AX6 → periodic root (existing A-tier conditional)

## New endpoints

| ID | Declaration | Source | Hypotheses |
|---|---|---|---|
| NC00 | NOETHER_CURRENT_REALIZATION | research only | actual physical current, not supplied |
| NC01 | NOETHER_CHARGE_ADMISSION | Admission.lean | normalized coercive dissipative charge, per finite horizon |
| NC02 | NOETHER_UNIFORM_PHYSICAL_ENSTROPHY | EnstrophyBound.lean | NC01 |
| NC03a | NOETHER_SIX_CHANNEL_MATCH | SixChannelBridge.lean | existing exact physical Parseval |
| NC03b | NOETHER_UNIFORM_SIX_ENSTROPHY | SixChannelBridge.lean | NC02, NC03a |
| NC04 | NOETHER_TO_AX6 | AX6Bridge.lean | NC03b and finite-interval lintegral |
| NC05 | NOETHER_CLOSURE | Root.lean | NC04, existing conditional NSE-B root |

No `axiom`, `sorry`, or change to the frozen underlying `Fefferman_B_0_adjust` contract is intended.

## Semantics

A normalized charge is assumed to dominate actual physical enstrophy. It may be
obtained from an unnormalized (c G_N \le Q_N\) with (c>0\) by replacing (Q_N\)
with (Q_N/c\) and adjusting the bound. Its construction from Noether's theorem
is NOT proved. Finite-window monotonicity suffices; an entire global conserved
current is not mathematically required for the conditional implication.

The premise is much stronger than ordinary NSE energy dissipation and should not
be confused with a consequence of time-translation symmetry.

## Reproduction

From the package root `regularity-B-assembly/Singular-Axiomatic-closure/` run
`SingularClosure/NoetherClosure/run.cmd` using the external native Windows
Lean 4.33.0 and the exact cached pinned Mathlib dependencies.

This audit checks only the NEW theorem declarations. The existing root's
pre-existing evidence is separate. Do not promote until source-pinned matching
external build and theorem-level standard-only audit both PASS.
