# REEMANIANS

This folder contains only endpoints that hold under the Riemann Hypothesis (RH).

| Folder | Exact endpoint | Native evidence | Marker |
| --- | --- | --- | --- |
| [BanachExt](BanachExt/) | `_root_.RiemannHypothesis → HXYThreeSpaces.BanachExt` | User-reported `PASS` | `!!!!(cond on RH)` |
| [HilbertRep](HilbertRep/) | `_root_.RiemannHypothesis → HXYThreeSpaces.HilbertRep` | User-reported `PASS` | `!!!!(cond on RH)` |
| [HolExt](HolExt/) | `_root_.RiemannHypothesis → HXYThreeSpaces.HolExt` | User-reported `PASS` | `!!!!(cond on RH)` |

```text
MODE := A_TIER_DERIVATION
SELECTED_ROOTS := {RH -> BanachExt, RH -> HilbertRep, RH -> HolExt}
CONSTRUCTION_INPUT := RiemannHypothesis
ADDITIONAL_RESEARCH_PREMISES := NONE
ENDPOINT_STATUS := A_TIER
VERIFIED_SOURCE_REVISION := FIX6
EVIDENCE_ORIGIN := USER_REPORTED_NATIVE_WINDOWS_PASS
ALLOWED_AXIOMS := {propext, Classical.choice, Quot.sound}
```

## Reproduction

| Folder | Command from that folder | Default selection |
| --- | --- | --- |
| [BanachExt](BanachExt/) | `run.cmd` | `C1` |
| [HilbertRep](HilbertRep/) | `run.cmd` | `C2` |
| [HolExt](HolExt/) | `run.cmd` | `C3` |

```text
PROJECT_SOURCE_COMPLETENESS := EACH_FOLDER_INDEPENDENT
PROJECT_LEAN_FILES_PER_FOLDER := 127
SIBLING_FOLDER_DEPENDENCIES := NONE
EXTERNAL_COMPILER := NATIVE_WINDOWS_LEAN_4.33.0
EXTERNAL_MATHLIB := EXISTING_PINNED_CACHE
MATHLIB_COMMIT := db584cd6d46c92f209a44c0f1c829460d327499d
CACHE_POLICY := TRUSTED_FAST_V2
RUNTIME_HASHING := NONE
POST_VALIDATION_PROOF_SOURCE_CHANGES := 0
ASSISTANT_LOCAL_LEAN_EXECUTIONS := 0
```

## Scope records

| Selected endpoint | Current scope | Native PASS provenance |
| --- | --- | --- |
| BanachExt | [ENDPOINT.json](BanachExt/ENDPOINT.json) | [FIX6 transcript](BanachExt/provenance/native-transcript-FIX6-pass.txt) |
| HilbertRep | [ENDPOINT.json](HilbertRep/ENDPOINT.json) | [FIX6 transcript](HilbertRep/provenance/native-transcript-FIX6-pass.txt) |
| HolExt | [ENDPOINT.json](HolExt/ENDPOINT.json) | [FIX6 transcript](HolExt/provenance/native-transcript-FIX6-pass.txt) |

```text
ENDPOINT.json := CURRENT_SELECTED_ENDPOINT_SCOPE
STATUS.json := PRESERVED_ORIGINAL_PACKAGE_STATUS
README.txt := PRESERVED_ORIGINAL_PACKAGE_DOCUMENTATION
FROZEN_CANDIDATES.json := PRESERVED_FREEZE_RECORD
```
