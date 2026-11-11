# H12 small-data physical closure — A-tier route

`PLAN_REVISION=1`  
`SOURCE_REVIEW=cf550b0e41097f2a72740b2147621e1dd4028dc5`  
`BASELINE=29 audited declarations`  
`PHYSICAL_GLOBAL_ROOT=OPEN`  
`NO_LOCAL_LEAN=TRUE`

This route extends `H12_SIGMA_ZERO_SMALL_PACKAGE`. The separate eleven-item
`Singular-Axiomatic-closure` ledger retains its own scope and identifiers.

## Completion rule

`[x]` = the stated item has matching completion evidence. Mathematical items
require the exact declaration, source revision/hash, external cached Lean
compiler PASS, exact-type PASS, and theorem-level axiom audit restricted to
`propext`, `Classical.choice`, `Quot.sound`.

`[ ]` = unresolved; a planned signature, prepared body, source import, or
successful unrelated theorem does not discharge the item. `A_TIER_CANDIDATE`
items remain unchecked. Any retained analytic/certificate premise is recorded
in the item and prevents unconditional promotion of the physical root.

On each completed item: change `[ ]` to `[x]`, attach the exact declaration and
evidence link in the completion ledger, and update `STATUS.txt`. A signature or
premise change reopens the affected item and dependent root claims until the
new exact contract passes. Scheduling does not change theorem scope.

## Certified base — completed

Common evidence: [exact 29-declaration manifest](ci/expected_axioms.json),
[frozen types](ci/Audit.lean),
[audit results](verification/ci_42941911087/audit.json),
[source hashes](verification/ci_42941911087/sources.sha256),
[compiler/audit provenance](verification/ci_42941911087/provenance.json),
[external run 42941911087](https://github.com/randogelist/Methlib/actions/runs/42941911087).
Final package replay: [run 42942572364](https://github.com/randogelist/Methlib/actions/runs/42942572364),
commit `225efa38d807ea3a8309a06305b76a8642dac761`.

- [x] **B01 — !! Fourier algebra.** `H12FourierFoundations.H12_FOURIER_FOUNDATIONS`: frequencies, solenoidal fibers, contractive Leray map, heat multiplier, finite projected transport.
- [x] **B02 — !! Spectral/absorption compilers.** `H12_SPECTRAL_ENERGY_BRIDGE`, `H12_CRITICAL_ABSORPTION`, `H12_CRITICAL_TRILINEAR_COMPILER`; exact supplied Sobolev/Holder premises retained.
- [x] **B03 — !! Integral and physical-data compilers.** The audited pairing, convection, Holder, component-Sobolev and HLS compiler roots in the manifest. The actual bounded Riesz-half operator is not a conclusion of these compilers.
- [x] **B04 — !! Real small coefficient carrier.** `H12SigmaZeroSmallClass.H12_SIGMA_ZERO_SMALL_CLASS`: conjugate reality, mean zero, solenoidality, heat/cutoff preservation.
- [x] **B05 — !! Scaling and nonzero admission.** `H12SmallScaling.H12_SMALL_SCALING`, `criticalNorm_scale`, `exists_small_positive_scale`.
- [x] **B06 — !! Coefficient L2 embedding.** `H12L2CoefficientEmbedding.H12_L2_COEFFICIENT_EMBEDDING`, `physical_frequency_gap`, `criticalNorm_eq_zero_iff`.
- [x] **B07 — !! Scalar differential bootstrap and budgets.** The six audited `H12CriticalEnergyBudget` declarations, including barrier persistence and uniform square-enstrophy bounds.
- [x] **B08 — !! Concrete admission to scalar budget.** The three audited `H12SmallClassBudget` declarations. Scalar trajectory hypotheses remain explicit.
- [x] **B09 — Cached verification infrastructure.** [workflow](../../.github/workflows/h12-sigma-zero-small.yml), `run.cmd`, exact-type/axiom audit, source-hash recheck; 21 checker-policy tests PASS. Windows runner syntax parsing PASS; native Windows execution of this runner is not claimed.

The nine entries group the existing evidence; they are not a completion
percentage for physical NSE regularity. No R-item below is discharged by a
scalar compiler alone.

## Frozen physical target

Let

\[
\lambda_k=2\pi|k|,\qquad
Q(a)=\sum_k\lambda_k|a_k|^2,\qquad
\mathsf{Small}_{\nu,C_3}(a)\iff
\nu>0\land C_3>0\land Q(a)<\left(\frac{\nu}{8C_3^3}\right)^2.
\]

Planned root: **`H12_SIGMA_SMALL_GLOBAL_REGULARITY`**.
The name is reserved here; its physical declaration is not yet implemented.

\[
\exists C_3>0\ \exists C_6>0:\quad
\mathsf{PhysicalSobolevBundle}(C_3)\ \land\
\mathsf{PhysicalH1L6}(C_6)\ \land\
\forall\nu>0\ \forall a:\mathsf{RealH12Datum},\quad
\mathsf{Small}_{\nu,C_3}(a)
\Longrightarrow \exists u,p:\ \mathsf{PhysicalConclusion}(\nu,C_6,a,u,p).
\]

`PhysicalSobolevBundle`, `PhysicalH1L6` and `PhysicalConclusion` are mathematical specifications
for R01-R03, not existing Lean constants. All their fields must be instantiated.
The constructed `C3` must satisfy all vector/tensor estimates used
by the nonlinear proof. An arbitrary positive numerical `C3` is insufficient.
The separately constructed `C6` satisfies the physical mean-zero estimate
\(\|f\|_6\le C_6\|\nabla f\|_2\); it enters the Serrin bound, not the admission radius.

`PhysicalConclusion` consists of:

\[
\partial_tu+(u\cdot\nabla)u+\nabla p=\nu\Delta u,\qquad
\operatorname{div}u=0,\qquad \overline u=0,\qquad \overline p=0;
\]
\[
u\in C([0,\infty);\dot H^{1/2}_{\sigma,0}),\quad
u\in L^2(0,\infty;\dot H^{3/2}_{\sigma,0}),\quad
\partial_tu\in L^2_{\mathrm{loc}}([0,\infty);\dot H^{-1/2}_{\sigma,0});
\]
\[
u(0)=\mathsf{Synth}(a),\qquad
u,p\in C^\infty((0,\infty)\times\mathbb T^3).
\]

The evolution must belong to the physical Leray-Hopf class. Velocity uniqueness
is required among all periodic Leray-Hopf solutions with that datum; equality
uses the declared weakly continuous representatives. Pressure is normalized
by zero spatial mean. Rough data require smoothness only for positive time.
Smooth data receive a separate classical-through-zero corollary.

Required quantitative outputs, with \(H_0=Q(a)\), are

\[
\|u(t)\|_{\dot H^{1/2}}^2+
\frac{3\nu}{2}\int_0^t\|u(s)\|_{\dot H^{3/2}}^2\,ds\le H_0,
\qquad
\|u(t)\|_{\dot H^{1/2}}^2\le e^{-6\pi^2\nu t}H_0;
\]
\[
\int_0^\infty\|\nabla u\|_2^4\,dt\le\frac{2H_0^2}{3\nu},\qquad
\int_0^\infty\|u\|_6^4\,dt\le\frac{2C_6^4H_0^2}{3\nu}.
\]

## Dependency spine

| Item | Prerequisites | Planned module |
|---|---|---|
| R01 | B01-B08 | `H12_PHYSICAL_CONTRACTS.lean` |
| R02 | R01, B01, B04-B06 | `H12_PHYSICAL_FOURIER_REALIZATION.lean` |
| R03 | R02, B02-B03 | `PERIODIC_RIESZ_HALF_L2_L3.lean` |
| R04 | R01, B01, B04, upstream finite ODE | `H12_GALERKIN_DATA_ADAPTER.lean` |
| R05 | R02-R04, B02-B03 | `H12_GALERKIN_CRITICAL_ENERGY.lean` |
| R06 | R05, B07-B08 | `H12_PHYSICAL_UNIFORM_BUDGET.lean` |
| R07 | R02-R06 | `H12_FOURIER_COMPACTNESS_AND_NSE_LIMIT.lean` |
| R08 | R07 | `H12_CRITICAL_TRACE_AND_GLOBAL_LIMIT.lean` |
| R09 | R08, physical H1-to-L6 estimate | `H12_SERRIN_CONTINUATION_AND_SMOOTHING.lean` |
| R10 | R08-R09 | `H12_LERAY_HOPF_UNIQUENESS.lean` |
| R11 | R01-R10 | `H12_SIGMA_SMALL_GLOBAL_REGULARITY.lean` |

These filenames are planned. Their appearance in this table does not assert
file existence or proof completion.

After R01, R02-R03 and the coefficient-level R04 adapter may proceed in parallel.
R05 joins those branches. R07-R08 construct the critical solution; R09 uses the
square-enstrophy estimate for actual continuation. R11 contains deterministic
composition of independently audited edges.

## Remaining physical work — unchecked

- [ ] **R01 — Freeze actual physical contracts and conversion signatures.**
  Specify the real torus field model, measures, Fourier convention, physical
  homogeneous Hilbert spaces for exponents \(-1/2,1/2,1,3/2\), distributional
  NSE, normalized pressure, Leray-Hopf solutions, trace and smoothness.
  Record every bridge between `CVec3`, component functions and upstream state
  spaces. Freeze exact root quantifiers and uniqueness class before bodies.
  Acceptance: compiled concrete definitions and exact-type checks; no assumed
  global solution or regularity field in the input contract.

- [ ] **R02 — Physical synthesis, representation and approximation.**
  Construct \(\mathsf{Synth}(a)\) from the square-summable coefficients and prove
  reality, mean zero, distributional divergence zero, Fourier recovery and
  \(\|\mathsf{Synth}(a)\|_{\dot H^{1/2}}^2=Q(a)\).
  Prove the converse representation for every physical datum in the target
  class, the required Hilbert-space/duality structure, and symmetric-cutoff
  convergence in the critical norm. Finite synthesis, derivative symbols,
  Parseval and multiplier commutation must match the chosen physical model.

- [ ] **R03 — Construct the physical critical Sobolev constant.**
  Primary route: mean-zero periodic heat kernel / Riesz-half representation,
  kernel bound, actual \(L^2_0\to L^3\) estimate, multiplier identification,
  and reconstruction. Instantiate `PeriodicRieszHalfCertificate` and each
  required component reconstruction; then reuse the audited component/HLS
  compiler with \(C_3=9C_{\mathrm{HLS}}>0\).
  Acceptance includes the exact common vector/tensor estimates for
  \(u,\nabla u,\Lambda u\). A genuine interpolation/Hilbert-scale alternative
  is admissible; elementary interpolation of the L2 and L6 function norms
  alone does not discharge the critical Sobolev theorem.

- [ ] **R04 — Admit rough critical coefficients to the actual finite ODE.**
  For every \(a,N\), construct the initial `InvariantGalerkinState N` from
  the canonical symmetric cutoff of \(a\). Prove reality, mean zero,
  solenoidality, coefficient conversions and physical frequency normalization.
  Reuse the actual invariant-state global ODE theorem where its audited
  contract applies. Obtain canonical trajectories, uniqueness and physical
  finite synthesis. Preserve the full `HasDerivAt` endpoint needed at time
  zero; an `Ici 0` within-derivative is a different interface obligation.

- [ ] **R05 — Prove the physical critical differential law.**
  With actual Galerkin trajectories define
  \(H_N=\|u_N\|_{\dot H^{1/2}}^2\),
  \(D_N=\|u_N\|_{\dot H^{3/2}}^2\),
  \(E_N=\|\nabla u_N\|_2^2\).
  Prove the differentiation, projection/pressure cancellations and pairing
  identifications giving
  \[
  \tfrac12H_N'+\nu D_N
  =-\langle (u_N\cdot\nabla)u_N,\Lambda u_N\rangle,
  \qquad
  |\langle (u_N\cdot\nabla)u_N,\Lambda u_N\rangle|
  \le C_3^3\sqrt{H_N}\,D_N.
  \]
  The supplied physical objects must instantiate the existing integral and
  Holder compilers. No critical differential law remains an input assumption
  at this endpoint.

- [ ] **R06 — Instantiate all scalar hypotheses and obtain actual budgets.**
  Discharge continuity, nonnegativity, derivative, initial cutoff contraction
  and \(E_N^2\le H_ND_N\). Apply B07-B08 to obtain, uniformly in \(N,T\),
  \[
  H_N(t)+\tfrac32\nu\int_0^tD_N\le H_0,\qquad
  \int_0^T E_N^2\le\frac{2H_0^2}{3\nu}.
  \]
  Also prove the finite critical exponential decay using the spectral gap.
  Acceptance: the actual NSE trajectories appear in the conclusion; scalar
  laws, physical equality certificates and trajectory existence are derived.

- [ ] **R07 — Quantitative compactness and actual nonlinear limit.**
  Derive \(\|B(u,v)\|_{\dot H^{-1/2}}\le
  C_3^3\|u\|_{\dot H^{1/2}}\|v\|_{\dot H^{3/2}}\), hence a uniform
  \(L^2_t\dot H^{-1/2}\) bound for \(\partial_tu_N\).
  Primary compactness route: finite-mode time compactness, a countable
  diagonal extraction, and the integrated tail estimate
  \[
  \int_0^T\sum_{\lambda_k>K}\lambda_k|\widehat u_N(k,t)|^2dt
  \le K^{-2}\int_0^T D_N(t)dt\quad(K>0).
  \]
  Prove strong \(L^2_t\dot H^{1/2}\) convergence, convergence of the physical
  nonlinear weak form, pressure reconstruction, and the physical Leray-Hopf
  energy inequality from zero and almost every positive starting time.
  The latter good-energy-time property is required for positive-time restarts.
  A general Aubin-Lions theorem is an optional replacement
  for the compactness edge, with the same output contract.

- [ ] **R08 — Strong critical trace, transferred bounds and one global curve.**
  Establish the Hilbert triple
  \(\dot H^{3/2}\subset\dot H^{1/2}\subset\dot H^{-1/2}\)
  with the \(\dot H^{1/2}\) pivot and its correct dual pairing. Prove the
  required time-continuity theorem, \(u(0)=\mathsf{Synth}(a)\), and
  \(u\in C_t\dot H^{1/2}\). Pass energy, decay and dissipation bounds to the
  limit. Use compatible diagonal extraction over integer horizons, or an
  explicitly proved restriction/gluing theorem, to construct one global
  evolution. Obtain infinite-time dissipation by monotone exhaustion.

- [ ] **R09 — Actual Serrin continuation and positive-time smoothness.**
  Construct/use an audited physical mean-zero H1-to-L6 estimate and derive
  \(u\in L^4(0,T;L^6)\), with
  \(\int_0^T\|u\|_6^4\le2C_6^4H_0^2/(3\nu)\).
  Prove the required local strong existence, periodic Serrin continuation and
  parabolic bootstrap endpoints. Choose a positive restart time simultaneously
  in the H3/2-slice set and the good-energy-time set. Construct a local strong
  evolution from that trace; prove a local strong-solution test/relative-energy
  comparison lemma identifying it with the restricted Leray-Hopf solution.
  Only after this identification transfer the Serrin bound to the strong
  evolution and prove continuation through every finite terminal time.
  Prove joint smoothness of
  velocity and normalized pressure. Local smoothing alone does not establish
  global continuation. Initial H1 regularity is not assumed for rough H1/2
  data. Any uniqueness lemma used in the restart argument must be proved as
  an independent edge, not assumed from the final root.

- [ ] **R10 — Rough-trace weak-strong uniqueness.**
  For the constructed \(u\) and every periodic Leray-Hopf solution \(v\)
  with the same datum, justify the relative-energy argument from time zero.
  With \(w=v-u\), derive a Gronwall inequality controlled by
  \(C\nu^{-3}\|u(t)\|_6^4\in L^1(0,T)\), and conclude equality on every
  finite interval. Audit the exact solution class and representative equality.
  The Serrin weak-strong comparison lemma may be developed in parallel with
  R09 after R08; its proof may not depend on the final uniqueness claim.

- [ ] **R11 — Assemble and audit the physical root.**
  Compose R01-R10 under the internally constructed Sobolev constant.
  Export both the coefficient-input theorem and the equivalent theorem
  quantified over every actual physical H1/2 solenoidal mean-zero datum,
  using the converse representation from R02.
  Discharge every existence, semantic, analytic, pressure, trace, continuation
  and uniqueness obligation in the frozen target. Add the smooth-data
  classical-through-zero corollary. Register the exact root and all new
  independent edges in `ci/Audit.lean` and `ci/expected_axioms.json`.
  Acceptance: cached external compiler PASS, exact root type PASS, standard-only
  axiom audit, matching source hashes, and no unresolved admission/certificate
  premises. Only then mark the physical root `!!!! UNCONDITIONAL_CLOSURE`.

## Optional export to the existing AX6 assembly

- [ ] **X01 — Physical small-data budget to the upstream AX6 interface.**
  After R04-R06, match the exact upstream datum domain; for the current smooth
  interface restrict to smooth mean-zero solenoidal data in the small ball.
  Prove the coefficient/physical enstrophy equality and the nonnegative
  Bochner interval-integral / ENNReal lintegral conversion on `Icc 0 T`,
  including endpoint-null-set handling. Then export the uniform budget to the
  actual AX6/six-channel statement. An arbitrary-data AX6 axiom is not a
  premise of the small-data physical route. X01 is not required by R11.

## Existing upstream interfaces — reuse, not task discharge

Source-review revision: `cf550b0e41097f2a72740b2147621e1dd4028dc5`.
Candidate source reuse requires exact compilation/audit evidence before any
new imported edge is promoted.

Upstream endpoint 3 has its own certified root:
`SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE`, tested commit
`c1af57143f708d3587a03425dbd9493db0e6f5f0`,
[external run 42940507715](https://github.com/randogelist/Methlib/actions/runs/42940507715).
Upstream endpoint 4, `SingularClosure.GALERKIN_ENERGY_IDENTITY`, also has
exact A-tier evidence at tested commit
`9ae282c28a7034e6f6c044a359205a7ae60380f1`,
[external run 42942665131](https://github.com/randogelist/Methlib/actions/runs/42942665131),
[exact audit](https://github.com/randogelist/Methlib/blob/cf550b0e41097f2a72740b2147621e1dd4028dc5/regularity-B-assembly/Singular-Axiomatic-closure/verification/9ae282c2_endpoint4.log).
The endpoint audit passed even though the unrelated aggregate failed. This
is an actual physical L2 energy identity, not the critical R05 energy identity.

The lower invariant-state existence lemmas and finite Parseval lemmas are
compiled dependencies of these certified roots; separate
named A-tier promotion requires their own exact-type/axiom audit. No matching
saved individual audits were identified for the finite Parseval or physical
L6 candidates listed below. R04 remains unchecked because the H12 adapter is absent.

| Upstream interface | Reuse target | Additional obligation |
|---|---|---|
| `SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE` | R04 reference root | Its physical datum premise is `SmoothSigmaZero`; rough critical data require an adapter |
| `SingularClosure.GALERKIN_ENERGY_IDENTITY` | R04/R07 physical L2 energy | Match the constructed `GalerkinSolution`; critical H1/2 energy remains R05 |
| `SingularClosure.invariantGalerkinRhs_global_exists` | R04 coefficient-state construction | `RealH12Datum` cutoff to `InvariantGalerkinState`; exact derivative/frequency correspondence |
| `FINITE_PHYSICAL_ENERGY_PARSEVAL`, `FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL`, `FINITE_PHYSICAL_ENSTROPHY_PARSEVAL` in `FiniteParseval.lean` | R02/R05/R06 | Match finite synthesis, coefficient representation and reality hypotheses |
| `PERIODIC_SOBOLEV_H1_L6`, `FINITE_PHYSICAL_L6_FROM_ENSTROPHY` in `PeriodicSobolev.lean` | R09 | Integer-order endpoint; does not itself discharge R03 |
| `SIX_CHANNEL_FINITE_ENSTROPHY_EQ`, `SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ` in `PhysicalParseval.lean` | X01 | Match energy definitions, datum domain and integral representation |

Both package roots currently pin Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. Reuse must preserve the standalone
package's import/dependency closure and cached Windows replay. Source presence
and matching toolchains do not establish adapter correctness.

## Execution and evidence ledger

Next work: **R01**, then **R02/R03** and **R04** in parallel where their exact
contracts permit. Endpoint signatures precede independent edge bodies;
deterministic composition follows. Cached external Lean elaboration may run
independent modules concurrently. Pending signatures remain unproved until
their bodies pass the external kernel.

| Completed item | Exact evidence | Physical-root effect |
|---|---|---|
| B01-B08 | 29-declaration audit and source manifest linked above | Certified coefficient/scalar/compiler base |
| B09 | Successful external package runs; checker tests; source recheck | Reproducible verification infrastructure |
| R01-R11 | None yet | Physical root remains OPEN |
| X01 | None yet | Upstream AX6 export remains OPEN |

For each future R/X completion append:

```text
ITEM=<Rxx or Xxx>
DECLARATIONS=<fully qualified names>
EXACT_TYPE=<audit source location>
TESTED_COMMIT=<full SHA>
SOURCE_HASHES=<manifest link>
EXTERNAL_RUN=<URL>
COMPILE=PASS
EXACT_TYPE_CHECK=PASS
AXIOMS=<observed list>
REMAINING_PREMISES=<explicit list or NONE>
CHECKBOX_CHANGE=[ ] -> [x]
```

Historical mathematical notes provide proof intentions. Their old candidate
labels and percentage estimates are not the completion authority for this
route. The exact audited declarations and this evidence ledger govern updates.
