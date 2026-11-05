# Fefferman A obstruction — literature-conditional

`!!!! (conditional on Literature)` · `!!! CONDITIONAL_FORMAL_CLOSURE`

| Field | Value |
| --- | --- |
| Exact root | `CondFeffA.Literature.WJI_LITERATURE_CONDITIONAL_CLOSURE` |
| External native compiler | Lean 4.33.0 |
| Reported build | `RUN=PASS` |
| Reported theorem audit | `STANDARD_ONLY` |
| Sole unresolved input | `CondFeffA.Literature.LiteratureSchwartzSlabRegularity` |
| Scope A | Literal v0.25.0 whole-space analytic-at-initial-time endpoint |
| Scope C | No `Fefferman.C` theorem asserted or audited in this package |
| Classical smooth Fefferman A | Not refuted |
| Premise-free closure | Open |

## Exact theorem

```lean
theorem WJI_LITERATURE_CONDITIONAL_CLOSURE
    (hLiterature : LiteratureSchwartzSlabRegularity) :
    (∃ c ∈ Ioo (0 : ℝ) 1,
      admissibleInitial realAnalysis .wholeSpace (datum c) ∧
      ¬ FactorialJetBound (fun n => (jetPolynomial n).eval c) ∧ ¬ GlobalAt c) ∧
    ¬ WholeSpaceZeroForceGlobalRegularity ∧ ¬ Fefferman.A realAnalysis
```

[Exact Lean source](WJI_LITERATURE_CONDITIONAL_CLOSURE.lean) · [Theorem manifest](WJI_LITERATURE_CONDITIONAL_CLOSURE_A_TIER.txt)

The same input yields `∀ᵐ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → ¬ GlobalAt c`.

## Literature input

`LiteratureSchwartzSlabRegularity` requires finite uniform spatial L² and L∞
bounds, almost everywhere on each positive-time slab, for every time derivative
and each finite collection of spatial derivative words of a smooth finite-energy
solution with the specified Schwartz initial datum.

The input is an explicit theorem argument. It is neither a new Lean axiom nor an
imported proof of the cited analysis. Its proposed derivation uses Tao,
*Localisation and compactness properties of the Navier–Stokes global regularity
problem*, Analysis & PDE 6 (2013), Corollaries 11.1 and 4.3, Theorem 5.4(iv),
Sobolev embedding, and correspondence with the literal slab definition.
[Paper](https://msp.org/apde/2013/6-1/apde-v6-n1-p02-s.pdf) ·
[DOI](https://doi.org/10.2140/apde.2013.6.25)

The qualified marker means that a kernel-checked, standard-axiom-only proof of
this exact input closes the remaining premise of this exact endpoint.
Unqualified `!!!!` remains open. Parsing alone does not discharge the input.

## Native verification

[Supplied console receipt](verification/native-output.txt) records `EXACT_ROOT=PASS`,
five theorem audit passes, and `RUN=PASS`. Evidence provenance: user-supplied
native Windows Lean 4.33.0 transcript; no local Lean execution. The excerpt does
not include an evidence-directory identifier or source-digest receipt.

The root source, runner, dependency sources, manifests and audit checker preserve
the distributed package bytes. [SHA-256 inventory](verification/SHA256SUMS.txt)
records the publication payload. The status manifest and this documentation
record the subsequent external result.

## Cached Windows reproduction

From this directory, using the existing native Lean 4.33.0 and Mathlib cache:

```cmd
call run.cmd
```

Optional cache-location arguments:

```cmd
call run.cmd /reuse "C:\path\to\prior\evidence\run" /mathlib "C:\path\to\mathlib\.lake\build\lib\lean"
```

The runner checks 57 modules, reuses matching prior objects, compiles missing
project objects, and reruns the root and five theorem audits. Its internal
package identifier remains `WJI_LITERATURE_CONDITIONAL_433`. Runtime `cache/`
and `evidence/` directories are not committed.

Original archive: `WJI_LITERATURE_CONDITIONAL_433.zip`

SHA-256: `7b8c78212f8c688f3e34d9869b3fe962f341f0997c8f78915fd3682b81c4806e`
