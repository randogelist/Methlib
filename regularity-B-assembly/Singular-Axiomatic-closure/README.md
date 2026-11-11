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
| 3 | `GALERKIN_GLOBAL_EXISTS_UNIQUE` | !=! A_TIER |
| 4 | `GALERKIN_ENERGY_IDENTITY` | !=! A_TIER |
| 5 | `GALERKIN_ENSTROPHY_INEQUALITY` | Pending |
| 6 | `CUBIC_ENERGY_OF_SQUARE_BUDGET` | !=! A_TIER |
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

## Verified checkpoint

Commit `bb7c4f569a7b305935006dfc333b17f1528ae34c`: all eight modules and their aggregate compiled; sixteen exact-type and theorem-level axiom audits passed with standard axioms only.

Evidence: https://github.com/randogelist/Methlib/actions/runs/42935149091

Frozen endpoints completed: **1/11**, namely endpoint 6. Spectral identities and finite physical reconstruction are verified auxiliary results; the complete physical projection/enstrophy endpoints remain pending. The general-data Galerkin existence, energy estimates, strong limit, smooth bootstrap, pressure recovery, and root implication remain open.

The preserved audit transcript and source hashes are in `verification/`. Exact scope for endpoint 6 is recorded in `CUBIC_ENERGY_OF_SQUARE_BUDGET_A_TIER.txt`. Full endpoint status is in `ENDPOINTS.json` and `Singular_Axiomatic_Closure_A_TIER.txt`; implementation corrections are in `CORRECTIONS.md`.

## Verified global Galerkin endpoint

Commit `c1af57143f708d3587a03425dbd9493db0e6f5f0`: frozen endpoint 3 passed the independent compiler, exact-type and theorem-level standard-only axiom audit. The trajectory exists for every positive viscosity, every concrete smooth solenoidal mean-zero input and every cutoff. Uniqueness is equality on nonnegative time, the actual trajectory domain.

Evidence: https://github.com/randogelist/Methlib/actions/runs/42940507715

The aggregate project build at that revision remained in repair for other modules. This checkpoint promotes only the independently audited endpoint 3. Frozen endpoint total at this checkpoint: 2/11 (3 and 6). No global PDE closure is inferred.

## Verified physical energy endpoint

Commit `9ae282c28a7034e6f6c044a359205a7ae60380f1`, run https://github.com/randogelist/Methlib/actions/runs/42942665131: endpoint 4 compiled and passed its exact-type and theorem-level standard-only axiom audit. The equality uses actual physical cube integrals, actual initial Fourier cutoff, and proved finite-time dissipation integrability. No energy-cancellation assumption appears.

Current independently verified endpoint total: **3/11**, endpoints 3, 4 and 6. The aggregate build remains in repair; no other endpoint is promoted.
