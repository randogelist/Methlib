# QFA endpoint and chain verification

| Field | Verified value |
|---|---|
| Exact scope | LE001–LE108 |
| Compiler | Native Windows Lean 4.33.0 |
| Theorems / proof-carrying constructions | 106 / 2 |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` |
| First successful LE001–LE093 source commit | `97d745678734a2bb9d7c1d9d4ae05d1a36c0a162` |
| First successful LE001–LE093 CI run | [43528295686](https://github.com/randogelist/Methlib/actions/runs/43528295686) |
| Current-manifest compiled commit | `9b6ca616b2f26e0222decb872401752e8320babe` |
| Current-manifest successful CI run | [43532773061](https://github.com/randogelist/Methlib/actions/runs/43532773061) |
| Current-manifest evidence | [VERIFICATION.txt](9b6ca616b2f26e0222decb872401752e8320babe/VERIFICATION.txt) |
| Physical QFA root | `B_TIER_ROOT_FORMALIZATION_PENDING` |
| Analytic targets | LC001/LC003/LC004 unresolved; LC001 → LC002 conditional only |
| Physical assembly obligations | AO01–AO08; unresolved |

## Verified executions

| Compiled commit | Execution | Manifest and source relation | Record |
|---|---|---|---|
| `97d745678734a2bb9d7c1d9d4ae05d1a36c0a162` | `43528295686`, attempt 1; completed / success | LE001–LE093; first exact external compiler and axiom success; endpoint status metadata subsequently promoted | [Verification](97d745678734a2bb9d7c1d9d4ae05d1a36c0a162/VERIFICATION.txt) |
| `9022b0365a605b64f8b1d630be1da0bcc5d3310f` | `43529398230`, attempt 1; completed / success | LE001–LE093; exact byte match to its verified v0.3.0 manifest and every listed runtime source | [Verification](9022b0365a605b64f8b1d630be1da0bcc5d3310f/VERIFICATION.txt) |
| `9b6ca616b2f26e0222decb872401752e8320babe` | `43532773061`, attempt 1; completed / success | LE001–LE108; exact current v0.4.0 manifest and runtime-source byte match | [Verification](9b6ca616b2f26e0222decb872401752e8320babe/VERIFICATION.txt) |

Current endpoint-manifest SHA256:
`e05a8d02127334c2b9332a9cd768205181b51bf43eb572288ed9f5069e50a39c`.

Current approved expected-registry SHA256:
`016016b2a771603da7d7c54749a77ee7b00a394ce6e4b4466e4d53b86baf95b8`.

Current immutable record-sha256.json SHA256:
`24a114573f4b3c927e9c301db9a9c4298b1503d9e47b0710b6291570baf8f383`.

Current-run downloaded evidence artifact: `14088656267`.
Artifact ZIP SHA256:
`a67614266bce9ae2e3c1a88d49cfc3a168431846e861f929d0a65b26fe9fa1a6`.

Historical v0.3.0 run `43529398230` downloaded evidence artifact: `14086493725`.
Artifact ZIP SHA256:
`36b4945d44cb93108bf51c9a3193dba2f289c82ef038274440a06176d9ff420a`.

The current status finalization changes only the outside-package chain ledger,
root README, indexed derivation status metadata, this CI index, and the new
`CI/9b6ca616b2f26e0222decb872401752e8320babe/` evidence record. Every LeanEndpoints file, workflow,
compiled runtime source, source manifest and exact declaration signature remains
unchanged. Both earlier successful evidence directories remain immutable.

## Evidence integrity

Evidence directories preserve original compiler output, exact compiler types,
transitive axiom reports, tested source manifests, dependency identities,
clean dependency snapshots, and GitHub run metadata.

`record-sha256.json` binds the recorded bytes. `.gitattributes` disables
line-ending conversion for these immutable execution records.

Source and package candidate labels record preparation history.
[The current chain ledger](../QUASI_FEFFERMAN_A_CHAIN_A_TIER.txt) and this matching evidence
identify all 108 externally verified declarations. The physical root and
AO01–AO08 remain unresolved; ReferenceConstructionFromAbsorption and the
class/reference interpretations remain explicit inputs.
