# Singular-Axiomatic-closure

Target: `SingularClosure.Fefferman_B_0_adjust` on the unit three-torus, with zero forcing and arbitrary smooth, solenoidal, mean-zero initial data.

The frozen unresolved analytic premise is a finite-time square-enstrophy budget, uniform in the Fourier-Galerkin cutoff. The intended root is `AX6Statement → Fefferman_B_0_adjust`.

## Verification boundary

This is an active formalization. Definitions and auxiliary lemmas do not constitute the conditional closure. The final physical implication has not been proved. No unproved PDE bridge is installed as an axiom or as a hidden root argument.

Lean executes only in external GitHub Actions, using Lean 4.33.0 and the pinned Mathlib object cache. Local Lean executions: zero. A successful CI audit verifies only its enumerated declarations at the tested commit. It does not complete a frozen endpoint unless its entire stated scope is covered.

Completion marker: `!=!`, assigned only after matching compiler and theorem-level axiom-audit evidence.

## Frozen endpoints

Foundation outside the numbered list: `PERIODIC_NSE_CONTRACTS`.

| # | Endpoint | Status |
|---:|---|---|
| 1 | `SIX_CHANNEL_PROJECTIONS` | Pending |
| 2 | `SIX_CHANNEL_ENSTROPHY_EQ` | Pending |
| 3 | `GALERKIN_GLOBAL_EXISTS_UNIQUE` | Pending |
| 4 | `GALERKIN_ENERGY_IDENTITY` | Pending |
| 5 | `GALERKIN_ENSTROPHY_INEQUALITY` | Pending |
| 6 | `CUBIC_ENERGY_OF_SQUARE_BUDGET` | Pending |
| 7 | `AX6_UNIFORM_STRONG_BOUNDS` | Pending |
| 8 | `GALERKIN_GLOBAL_STRONG_LIMIT` | Pending |
| 9 | `GLOBAL_STRONG_SMOOTH_BOOTSTRAP` | Pending |
| 10 | `PERIODIC_PRESSURE_RECOVERY` | Pending |
| 11 | `ax6_implies_fefferman_B_0_adjust` | Pending |

The six channels are the ordered refinement with `j = 3`, `i = 1`: split each of `(v,w,r)` by averaging in `x₁` and its complement. Spectral algebra and its physical Fourier realization are tracked separately; only the full endpoint earns its frozen completion marker.

## Single-axiom boundary

For actual Galerkin trajectories, write

```text
E6_N(t) = sum A=1..6 ||grad(Q_A u_N(t))||_2^2 = ||grad u_N(t)||_2^2.
AX6: for every nu>0, smooth sigma-zero datum a, and T>0,
     there exists finite M(nu,a,T), independent of N,
     such that integral_0^T E6_N(t)^2 dt <= M(nu,a,T).
```

The intended pure implication must audit with standard Lean axioms only. Its final specialization may depend on exactly one additional named axiom, `AX6`. Standard-only axiom audits do not discharge hypotheses such as analytic endpoint records; exact root-type checks are also required.

The direct analytic chain is:

```text
AX6
 -> uniform accumulated H1/H2 estimate
 -> compactness and actual nonlinear passage
 -> global strong solution with initial trace
 -> smooth bootstrap and periodic pressure
 -> Fefferman_B_0_adjust.
```

## Current source scope

`Contracts.lean` defines actual periodic lifts, physical differential operators, and the unrestricted target. Its zero-datum lemmas are sanity checks only.

`SixChannels.lean` and `SixEnergy.lean` give concrete coefficient projections and exact extended nonnegative spectral energy identities. Physical Fourier synthesis and the gradient integral identity remain separate obligations.

`Galerkin.lean` defines the Euclidean frequency cutoff, actual Fourier coefficients of the initial datum, finite physical synthesis, and the projected NSE convolution ODE. Its zero-data trajectory proves nonvacuity only for that datum.

`Admission.lean` defines `AX6Statement` using the actual synthesized fields and nonnegative extended space-time integrals. It quantifies over all trajectories of the concrete ODE; equivalence with a canonical trajectory requires endpoint 3. No `AX6` axiom is declared at this stage.

`CubicBudget.lean` supplies the scalar integrating-factor argument for endpoint 6. Its analytic hypotheses are explicit; it does not supply the Galerkin energy estimate or the uniform budget.

The existing periodic-B and positive-time packages inspected during assembly do not supply endpoints 8--10: their global conclusions require a global flow or an extension premise. Compactness, nonlinear convergence, trace, pressure recovery, and smooth bootstrap therefore remain proof obligations here.

Full endpoint status and exact evidence will be maintained in `ENDPOINTS.json` and `Singular_Axiomatic_Closure_A_TIER.txt`. Significant implementation corrections are recorded separately in `CORRECTIONS.md`.
