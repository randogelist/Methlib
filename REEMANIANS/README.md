# REEMANIANS

This folder contains endpoints conditional on the Riemann Hypothesis (RH), together with finite-certificate reductions to RH. It also contains pinned source repositories for the related RH, generalized Dirichlet L-function, and Hilbert-vector-resolvent projects. Reduction projects state their admission premises explicitly; they do not assert an exhibited RH witness.

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

## Finite-certificate reductions

| Folder | Exact scope | Evidence | Status |
| --- | --- | --- | --- |
| [RH_REDUCTION_02](RH_REDUCTION_02/) | Finite Dodgson presieve; filtered acceptance implies RH; certified projections preserve original acceptance | [User-reported native PASS](RH_REDUCTION_02/provenance/user-reported-native-pass.txt) | Scoped A-tier; conditional formal closure |

`RH_REDUCTION_02/VERIFIED_STATUS.txt` records current verification scope. Original package documentation remains preserved as source provenance.

## Pinned source repositories

```text
SNAPSHOT_DATE := 2026-11-07
SNAPSHOT_SOURCE := DEFAULT_BRANCH_HEAD_AT_ADDITION
SUBMODULE_MODE := 160000
SUBMODULE_UPDATE_POLICY := EXPLICIT_COMMIT_UPDATE
PROOF_STATUS := AS_RECORDED_IN_EACH_PINNED_SOURCE
STATUS_PROMOTION_FROM_SUBMODULE_ADDITION := NONE
```

| Submodule | Source branch | Pinned commit | Source snapshot download |
| --- | --- | --- | --- |
| [Generalized-Dirichlet-L-Function-Hypothesis](Generalized-Dirichlet-L-Function-Hypothesis/) | `main` | [`c399936b0b1bba945db1e745dfc03801589d2ba1`](https://github.com/randogelist/Generalized-Dirichlet-L-Function-Hypothesis/commit/c399936b0b1bba945db1e745dfc03801589d2ba1) | [ZIP](https://github.com/randogelist/Generalized-Dirichlet-L-Function-Hypothesis/archive/c399936b0b1bba945db1e745dfc03801589d2ba1.zip) |
| [snditeration](snditeration/) | `main` | [`d451b066e5718d70a00358a73bd554e779e99677`](https://github.com/randogelist/snditeration/commit/d451b066e5718d70a00358a73bd554e779e99677) | [ZIP](https://github.com/randogelist/snditeration/archive/d451b066e5718d70a00358a73bd554e779e99677.zip) |
| [zetahyperbolic-axiom](zetahyperbolic-axiom/) | `main` | [`b56c8102d25b931a601992c93bf30b19cc7ee103`](https://github.com/randogelist/zetahyperbolic-axiom/commit/b56c8102d25b931a601992c93bf30b19cc7ee103) | [ZIP](https://github.com/randogelist/zetahyperbolic-axiom/archive/b56c8102d25b931a601992c93bf30b19cc7ee103.zip) |
| [Riemann-Hypothesis-Final](Riemann-Hypothesis-Final/) | `main` | [`ba58f416746517b865c06ebf64e75b283fbfe437`](https://github.com/randogelist/Riemann-Hypothesis-Final/commit/ba58f416746517b865c06ebf64e75b283fbfe437) | [ZIP](https://github.com/randogelist/Riemann-Hypothesis-Final/archive/ba58f416746517b865c06ebf64e75b283fbfe437.zip) |
| [Hilber-Vector-Resolvent-Theory](Hilber-Vector-Resolvent-Theory/) | `main` | [`29249c8ff158e97b20475320323206a29626e3b5`](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/commit/29249c8ff158e97b20475320323206a29626e3b5) | [ZIP](https://github.com/randogelist/Hilber-Vector-Resolvent-Theory/archive/29249c8ff158e97b20475320323206a29626e3b5.zip) |

### Checkout

```sh
git clone --recurse-submodules https://github.com/randogelist/Methlib.git
```

Existing checkout, from the Methlib root:

```sh
git pull --ff-only
git submodule update --init --recursive
```

Each submodule resolves to the exact commit recorded above. Later upstream commits require an explicit submodule-pin update in Methlib. The source snapshots preserve the files, documentation, and evidence already committed upstream; uncommitted files and external dependencies are outside the snapshot. GitHub's Methlib ZIP download excludes submodule contents; use recursive checkout or the individual source snapshot downloads.
