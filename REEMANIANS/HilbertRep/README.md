# HilbertRep

```text
SELECTED_ENDPOINT := C2
CONSTRUCTION_INPUT := _root_.RiemannHypothesis
ADDITIONAL_RESEARCH_PREMISES := NONE
STATUS := A_TIER
MARKER := !!!!(cond on RH)
CURRENT_SCOPE_RECORD := ENDPOINT.json
```

## Exact forward endpoint

```lean
HXYThreeSpaces.hilbertRep_of_nativeRH :
  _root_.RiemannHypothesis → HXYThreeSpaces.HilbertRep
```

[Forward source](HXYThreeSpaces/HilbertForward.lean) · [Selected endpoint record](ENDPOINT.json)

## Frozen predicate

```lean
def HilbertRep : Prop :=
  ∃ (H : Type) (instNorm : NormedAddCommGroup H),
    letI := instNorm
    ∃ instInner : InnerProductSpace ℂ H,
      letI := instInner
      ∃ instComplete : CompleteSpace H,
        letI := instComplete
        ∃ (T : H →L[ℂ] H) (v : H),
          IsSelfAdjoint T ∧ T.IsPositive ∧ (1 - T).IsPositive ∧
          ‖v‖ = 1 ∧
          ∀ n : ℕ, inner ℂ v ((T ^ n) v) = (actualNormalizedMoment n : ℂ)
```

## Equivalence reference

```lean
HXYThreeSpaces.nativeRH_iff_hilbertRep :
  _root_.RiemannHypothesis ↔ HXYThreeSpaces.HilbertRep
```

[Equivalence source](HXYThreeSpaces/Hilbert.lean)

```text
EQUIVALENCE_STATUS := A_TIER
EQUIVALENCE_MARKER := !!
SELECTED_PUBLICATION_ENDPOINT := RH -> HilbertRep
```

## Native evidence

| Field | Value |
| --- | --- |
| Origin | User-reported native Windows console excerpts |
| Verified source revision | `FIX6` |
| External exact-type check | `PASS` |
| External theorem-level axiom audit | `STANDARD_ONLY` |
| Native run | `PASS` |
| Allowed axiom set | `{propext, Classical.choice, Quot.sound}` |
| Raw native audit receipt files supplied | `FALSE` |

[FIX6 PASS transcript](provenance/native-transcript-FIX6-pass.txt) · [FIX5 supporting transcript](provenance/native-transcript-FIX5-partial.txt) · [Promotion record](provenance/promotion-FIX6.json)

## Native cached reproduction

```cmd
run.cmd
```

| Requirement | Value |
| --- | --- |
| Default selection | `C2` |
| External compiler | Native Windows x86_64 Lean `4.33.0` |
| Toolchain | `leanprover/lean4:v4.33.0` |
| External Mathlib cache | Existing cached checkout and packages |
| Mathlib commit | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Cache environment variable | `MATHLIB_CACHE_ROOT` |
| Default Mathlib cache | `%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1` |
| Shared compatible project cache | `%LOCALAPPDATA%\LEAN_ANCHORINGS\HXY_THREE_SPACES_433` |

```text
PROJECT_SOURCE_COMPLETENESS := SELF_CONTAINED
PACKAGED_LEAN_FILES := 127
SIBLING_FOLDER_DEPENDENCIES := NONE
RUNNER_POLICY := TRUSTED_FAST_V2
RUNTIME_HASHING := NONE
RECURSIVE_DEPENDENCY_INVENTORY := NONE
POST_VALIDATION_PROOF_SOURCE_CHANGES := 0
NATIVE_RUNNER_SOURCE_CHANGES := 0
LAUNCHER_DEFAULT_SELECTION := C2
ASSISTANT_LOCAL_LEAN_EXECUTIONS := 0
```

## Preserved source-package records

| Record | Scope |
| --- | --- |
| [ENDPOINT.json](ENDPOINT.json) | Current selected endpoint |
| [STATUS.json](STATUS.json) | Preserved original package status |
| [README.txt](README.txt) | Preserved original package documentation |
| [FROZEN_CANDIDATES.json](FROZEN_CANDIDATES.json) | Preserved freeze-time record |
| [Original launcher](provenance/run-FIX6.cmd) | Archived FIX6 launcher bytes |
| [Native runner](scripts/native-runner.js) | Preserved native runner source |
| [Frozen source manifest](provenance/frozen-sources.json) | Preserved upstream source identities |
| [New-source manifest](provenance/new-sources.json) | Preserved endpoint source identities |
| [SHA256SUMS.txt](SHA256SUMS.txt) | Archival file labels; runtime hashing disabled |
