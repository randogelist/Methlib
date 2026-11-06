# External verification record

```text
ROOT=AIM025.AIM025_CHOLLET_NONNEGATIVE
SOURCE_STATUS=A_TIER
SCOPED_CLOSURE=!!!! UNCONDITIONAL_CLOSURE
AUDITED_THEOREMS=36
AXIOM_STATUS=PASS_STANDARD_ONLY
UNRESOLVED_OBLIGATIONS_WITHIN_SCOPE=0
ORIGINAL_AIM025_CLOSURE=OPEN
LOCAL_LEAN_EXECUTIONS=0
LOCAL_LAKE_EXECUTIONS=0
PUBLICATION_COMPILER_RUN=NONE
```

## Source identity

| Item | SHA-256 / identity |
| --- | --- |
| `AIM025CholletNonnegative.lean` | `8d6371fb72c496f43400bb93ba73a9df96c9e1cdac3b9aa35b384197d47acd17` |
| FIX3 `Audit.lean` | `78914fadf40e5bb7cb453070c2f55e67978e66b2311a710ce6bda057a58460ac` |
| Original FIX3 source manifest | `3aafa00e5aa05a8304d5e3cf463f5c418e6a785118c26237a2f889a73fb332c1` |
| Original FIX3 ZIP | `679e2bde6d21810ded232f6391ce1bd1749d21ae2b24222df0795eecc5488bfd` |
| Native Lean | `4.33.0`, `x86_64-w64-windows-gnu` |
| Native Lean commit | `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| Reference Mathlib commit | `db584cd6d46c92f209a44c0f1c829460d327499d` |

The main source, FIX3 audit, native runner, toolchain file and audit target list are byte-identical to the reviewed FIX3 package. Publication documentation and status metadata have been adapted to the repository folder. This folder's `SHA256SUMS` is consequently a new publication manifest, separate from the original manifest identity above.

## Reviewed external evidence

1. The user-supplied FIX2 transcript records the exact native Windows compiler identity, matching source hashes, a successful source snapshot check, core compiler exit zero, all 36 standard-only theorem axiom reports and all 36 native guard pass markers. Audit compilation exited one because `set_option pp.width 140` was unsupported. That incomplete run was not accepted as a full pass.
2. FIX3 preserves the complete core source and removes exactly the unsupported audit formatting-option line. The successful user-supplied FIX3 completion excerpt contains the root signature and standard-only root axiom report, all 36 `AXIOM_AUDIT_PASS` markers, audit compiler exit zero and final success markers.
3. The acceptance review matched these records against the source identities and the exact native runner. The runner requires source snapshot hashes, its pinned core hash, the exact native version/target/commit, both compiler completions, all target reports and all native allowlist markers before reporting success.

The supplied FIX3 excerpt reports the following machine markers:

```text
AIM025_NATIVE_AXIOM_AUDIT_COUNT=36
AIM025_NATIVE_AXIOM_AUDIT=PASS_STANDARD_ONLY
NATIVE_EXIT=AUDIT:0
COMPILE_PASS=Audit.lean
EXTERNAL_COMPILER=PASS
NATIVE_THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY
AUDITED_THEOREM_COUNT=36
SCOPED_ROOT_EVIDENCE=READY_FOR_REVIEW
A_TIER_PROMOTION=REVIEW_REQUIRED
ORIGINAL_AIM025_CLOSURE=OPEN
FINAL_EXIT=0
```

These lines summarize the supplied result; this file is not a raw compiler log. The subsequent acceptance review establishes the accepted status for the exact source identities above. The root dependency report contains only `propext`, `Classical.choice` and `Quot.sound`; printed universe suffixes are parameters of those same declaration names. The guard rejects `sorryAx` and every axiom outside that allowlist.

## Evidence completeness

The full FIX3 evidence ZIP was not uploaded or inspected. Publication contains neither that ZIP nor raw user transcripts. The acceptance basis is the reviewed FIX2 core transcript, byte-identical FIX3 core source, successful FIX3 completion excerpt and known runner gates. No independent publication-time execution is claimed. The unchanged runner is provided for a fresh external native cached reproduction.

The exact quantified finite entrywise nonnegative theorem has no unresolved certificate, witness, checker, admission, semantic bridge or analytic endpoint. The unrestricted complex Hermitian PSD AIM025 statement and broader operator/HVR extensions remain outside this accepted scope.
