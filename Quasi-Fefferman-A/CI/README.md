# QFA endpoint verification

| Field | Verified value |
|---|---|
| Exact scope | LE001–LE093 |
| Compiler | Native Windows Lean 4.33.0 |
| Theorems / proof-carrying constructions | 91 / 2 |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` |
| First successful source commit | `97d745678734a2bb9d7c1d9d4ae05d1a36c0a162` |
| First successful CI run | [43528295686](https://github.com/randogelist/Methlib/actions/runs/43528295686) |
| Current-manifest compiled commit | `9022b0365a605b64f8b1d630be1da0bcc5d3310f` |
| Current-manifest successful CI run | [43529398230](https://github.com/randogelist/Methlib/actions/runs/43529398230) |
| Current-manifest evidence | [VERIFICATION.txt](9022b0365a605b64f8b1d630be1da0bcc5d3310f/VERIFICATION.txt) |
| Physical QFA root | `B_TIER_ROOT_FORMALIZATION_PENDING` |
| Analytic targets | LC001–LC004; no supplied proof inhabitants |
| Physical assembly obligations | AO01–AO08; unresolved |

## Verified executions

| Compiled commit | Execution | Manifest and source relation | Record |
|---|---|---|---|
| `97d745678734a2bb9d7c1d9d4ae05d1a36c0a162` | `43528295686`, attempt 1; completed / success | First exact external compiler and axiom success; endpoint status metadata subsequently promoted | [Verification](97d745678734a2bb9d7c1d9d4ae05d1a36c0a162/VERIFICATION.txt) |
| `9022b0365a605b64f8b1d630be1da0bcc5d3310f` | `43529398230`, attempt 1; completed / success | Exact byte match to the current manifest and every listed runtime source | [Verification](9022b0365a605b64f8b1d630be1da0bcc5d3310f/VERIFICATION.txt) |

Current endpoint-manifest SHA256:
`11897966f21632c9b8e107f8640677206598404048a97f3f866164840cbad475`.

Current-run downloaded evidence artifact: `14086493725`.
Artifact ZIP SHA256:
`36b4945d44cb93108bf51c9a3193dba2f289c82ef038274440a06176d9ff420a`.

The final evidence-recording commit changes only this index and
`CI/9022b0365a605b64f8b1d630be1da0bcc5d3310f/`. Compiled runtime sources,
the source manifest, exact declaration signatures and the frozen root remain
identical to the current-manifest successful execution.

## Evidence integrity

Evidence directories preserve original compiler output, exact compiler types,
transitive axiom reports, tested source manifests, dependency identities,
clean dependency snapshots, and GitHub run metadata.

`record-sha256.json` binds the recorded bytes. `.gitattributes` disables
line-ending conversion for these immutable execution records.

Source-header candidate labels record preparation history. The endpoint ledger
and matching evidence identify the externally verified declarations.
