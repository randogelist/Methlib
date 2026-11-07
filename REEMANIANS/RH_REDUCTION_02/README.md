# RH_REDUCTION_02

```text
STATUS=A_TIER
CLOSURE=CONDITIONAL_FORMAL_CLOSURE
MARKERS=!!_AND_!!!
EVIDENCE=USER_REPORTED_NATIVE_WINDOWS_PASS_AND_STANDARD_ONLY_AXIOM_AUDIT
TOOLCHAIN=Lean_4.33.0
```

## Exact scope

```text
checkPruned(W) := necessaryDodgsonTests(W) && originalCheck(W).

checkPruned(W)=true -> RiemannHypothesis.

CertifiedDodgsonProjection(F) ->
  checkPruned(F,W)=originalCheck(W).
```

The scoped implication, finite rational Dodgson tests, strict-cell family exclusions, and certified-projection preservation endpoints have user-reported external compilation and standard-only theorem-axiom-audit evidence. The original checker-to-RH chain remains intact.

```text
RH_WITNESS_EXHIBITED=FALSE
NONTRIVIAL_ACTUAL_XI_TO_RATIONAL_CELL_PROJECTION=NOT_INSTANTIATED
UNCONDITIONAL_RH_CLOSURE=NOT_ESTABLISHED
UNIVERSAL_NUMERICAL_TAIL_CHECKER=OPEN
```

## Native cached run

From the Methlib repository root in Windows `cmd.exe`:

```cmd
cd /d "REEMANIANS\RH_REDUCTION_02" && call run.cmd
```

```text
DEPENDENCIES=CACHED_NATIVE_WINDOWS_LEAN_4.33_AND_MATHLIB
NETWORK=NOT_USED
LAKE=NOT_USED
CUSTOM_SOURCE_DEPENDENCIES=INCLUDED_IN_THIS_DIRECTORY_AND_backend
CROSS_FOLDER_CUSTOM_SOURCE_DEPENDENCY=NONE
CACHE_REUSE=SOURCE_AND_TOOLCHAIN_MATCHED
```

The package includes its custom backend source closure. Existing external Mathlib and toolchain caches remain required. `run.cmd` invokes the packaged Python runner and records new evidence under `_evidence`.

## Provenance and status precedence

- [VERIFIED_STATUS.txt](VERIFIED_STATUS.txt): current scoped status and unresolved premises.
- [provenance/user-reported-native-pass.txt](provenance/user-reported-native-pass.txt): supplied transcript excerpt, with its original truncated first line preserved.
- [provenance/SOURCE_ASSOCIATION.txt](provenance/SOURCE_ASSOCIATION.txt): source association, hashes, counts, and evidence limitations.

All 161 files from the published candidate archive are preserved byte for byte, including the original `source-manifest.json` and candidate-status documents. Their pending-status statements are frozen preparation history. `VERIFIED_STATUS.txt` records the subsequent external PASS and is authoritative for the current scoped status.

```text
ORIGINAL_PACKAGED_FILES=161
ORIGINAL_LEAN_FILES=148
REACHABLE_CUSTOM_DAG_MODULES=114
CONFIGURED_THEOREM_AUDIT_ROOTS=98
CONFIGURED_NEGATIVE_CONTROLS=7
LOCAL_ASSISTANT_LEAN_EXECUTION=NONE
```
