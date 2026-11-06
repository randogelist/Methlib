# AIM939 — diagonal concavity counterexample

**Status: `!!!! UNCONDITIONAL_CLOSURE` for `¬ AIM939.DiagonalConcavityAssertion4`.**

| Field | Value |
| --- | --- |
| Root theorem | `AIM939.AIM939_COUNTEREXAMPLE` |
| Exact scope | Counterexample at `n = p = 4` |
| Coefficients | `(1, 2, 3, 5, 1)`, all strictly positive |
| Accepted formal status | `A_TIER` |
| Theorem-level axiom audit | 12 / 12, standard axioms only |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Unresolved obligations within the exact root | 0 |
| Native compiler | Lean 4.33.0, `x86_64-w64-windows-gnu` |
| Source conjecture | Universal diagonal-to-full-concavity implication refuted by this instance |
| Public AIM catalogue admission | Not established |

## Exact theorem

```lean
AIM939.exists_counterexample :
  ∃ a : Fin 5 → ℝ,
    (∀ k, 0 < a k) ∧
    ConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun t => AIM939.rootQuarter (AIM939.fOf a (fun _ => t))) ∧
    ¬ ConcaveOn ℝ AIM939.orthant
      (fun x => AIM939.rootQuarter (AIM939.fOf a x))

AIM939.AIM939_COUNTEREXAMPLE : ¬ AIM939.DiagonalConcavityAssertion4
```

Let `σₖ` denote the ordinary unnormalized elementary symmetric sums. The witness is

$$
f(x)=1+2\sigma_1(x)+3\sigma_2(x)+5\sigma_3(x)+\sigma_4(x),
\qquad P(t)=f(t,t,t,t)=1+8t+18t^2+20t^3+t^4.
$$

The fourth root of `P` is concave on the entire interval `(0, ∞)`. The fourth root of `f` violates the midpoint concavity inequality at strictly positive points. Every coefficient, domain, analytic and finite-witness obligation is discharged within the formal proof. The [B-tier derivation](AIM939_DIAGONAL_CONCAVITY_COUNTEREXAMPLE_B_TIER.txt) contains the exact polynomial curvature identity and rational fourth-root bounds.

The [frozen AIM939 statement](https://github.com/MColbrook/AIM/blob/4f5b1659355cb61d194da94ef14615214e1363a8/problems/939-diagonal-concavity-for-sums-of-elementary-symmetric-polynomials.md) quantifies over `1 ≤ p ≤ n` and permits `n = p = 4`. Thus this instance mathematically refutes that universal implication. The Lean root formalizes the negation of its four-variable specialization. No real-rootedness hypothesis occurs in the target. Source correspondence is recorded in [AIM939_SOURCE_SCOPE.txt](AIM939_SOURCE_SCOPE.txt).

## Files

| File | Content |
| --- | --- |
| [AIM939_COUNTEREXAMPLE.lean](AIM939_COUNTEREXAMPLE.lean) | Existential counterexample and exact negative root |
| [AIM939/Core.lean](AIM939/Core.lean) | Definitions, coefficients, diagonal identity and target assertion |
| [AIM939/Diagonal.lean](AIM939/Diagonal.lean) | Global diagonal concavity |
| [AIM939/FiniteWitness.lean](AIM939/FiniteWitness.lean) | Exact interior midpoint violation |
| [Audit.lean](Audit.lean) | Transitive theorem-level axiom allowlist guard |
| [AIM939_COUNTEREXAMPLE_A_TIER.txt](AIM939_COUNTEREXAMPLE_A_TIER.txt) | Accepted exact scope and closure record |
| [AIM939_DIAGONAL_CONCAVITY_COUNTEREXAMPLE_B_TIER.txt](AIM939_DIAGONAL_CONCAVITY_COUNTEREXAMPLE_B_TIER.txt) | Complete mathematical derivation |
| [evidence/VERIFICATION.md](evidence/VERIFICATION.md) | External evidence summary and acceptance basis |
| [audit-theorems.txt](audit-theorems.txt) | Exact 12-target audit list |
| [run.cmd](run.cmd) | Native cached Windows reproduction and evidence capture |
| [package.json](package.json) | Machine-readable status and source identities |
| [sources.sha256](sources.sha256) | Publication file-integrity manifest |
| [checks/EXACT_RATIONAL_CHECK.json](checks/EXACT_RATIONAL_CHECK.json) | Supplementary exact arithmetic record |

## Cached native Windows reproduction

Requirements: an existing native Lean 4.33.0 compiler and a compatible, already compiled Mathlib cache. Defaults:

```text
LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe
CACHE_ROOT=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1
```

From the repository root, in Windows CMD:

```bat
call "AIM_LEAN_SNIPES\AIM939\run.cmd"
```

Optional overrides: `AIM939_LEAN_EXE`, `AIM939_CACHE_ROOT`, `AIM939_THREADS` (default `16`). `AIM939_CACHE_ROOT` denotes an existing project containing `.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean` and compatible dependency caches.

The unchanged runner verifies `sources.sha256`, checks Lean version `4.33.0`, compiles the four proof modules into a fresh evidence directory, and executes the 12-target audit. Its fresh build directory precedes cached dependencies in `LEAN_PATH`. No dependency acquisition or dependency rebuilding occurs. Fresh run outputs are written beneath `evidence/r-*` and excluded by `.gitignore`.

Expected terminal markers:

```text
AIM939_THEOREM_AUDIT=PASS_STANDARD_ONLY
AIM939_NATIVE_RESULT=PASS
```

The runner retains its original package label `AIM939_DIAGONAL_CONCAVITY_COUNTEREXAMPLE_433_v0_1_0_FIX3`. The five Lean files, runner and toolchain declaration preserve their accepted source bytes. `.gitattributes` disables line-ending conversion. Publication documentation and the manifest are adapted to this directory. Historical candidate-status comments in the frozen Lean source are superseded by the accepted status record.

## External evidence basis

Acceptance uses the matching user-supplied FIX3 native Windows transcript, which reports all four proof compilations, all 12 theorem axiom audits and both terminal success markers. The complete raw evidence directory, external source-hash log and compiled objects were not separately received. Successful source gating is inferred from the unchanged runner's mandatory checks and the retained original package. Public evidence is a summary; raw personal filesystem paths are omitted.

No local Lean/Lake execution or publication-time compiler rerun is claimed. The actual external Mathlib Git revision was not measured. Historical priority, human peer review, public AIM catalogue admission and the catalogue-specific Linux verification procedure are not established by this publication. See [VERIFICATION.md](evidence/VERIFICATION.md).
