# External verification record

```text
ROOT=AIM939.AIM939_COUNTEREXAMPLE
ROOT_TYPE=NOT AIM939.DiagonalConcavityAssertion4
SOURCE_STATUS=A_TIER
SCOPED_CLOSURE=!!!! UNCONDITIONAL_CLOSURE
EXACT_SCOPE=N_EQ_P_EQ_4_COUNTEREXAMPLE
AUDITED_THEOREMS=12
AXIOM_STATUS=PASS_STANDARD_ONLY
UNRESOLVED_OBLIGATIONS_WITHIN_ROOT=0
ORIGINAL_UNIVERSAL_IMPLICATION=REFUTED_BY_EXPLICIT_INSTANCE
PUBLIC_AIM_CATALOGUE_ADMISSION=NOT_ESTABLISHED
EVIDENCE_ID=r-22262-14523-14555
LOCAL_LEAN_EXECUTIONS=0
LOCAL_LAKE_EXECUTIONS=0
PUBLICATION_COMPILER_RUN=NONE
```

## Source identity

| File | SHA-256 |
| --- | --- |
| `AIM939/Core.lean` | `437835bf7a64ad326f382d104ad0086254d7bc9341240799639aecb62aa70575` |
| `AIM939/Diagonal.lean` | `1cc1a3c046bde701209ff27f9c508a9a6d706bf3c329e384e488ea6146f06852` |
| `AIM939/FiniteWitness.lean` | `8aa33ef387c052bf239223e795f81d7cf176c21a0161154c315f36c3d70909bc` |
| `AIM939_COUNTEREXAMPLE.lean` | `eaf22f61cf830750dfb5bb14401fb6bc2a020507baefc0189175478717826318` |
| `Audit.lean` | `7e4d876d8735242acf42164301028b30c957ccf61a4f6044b9e74369a01dcaa7` |
| `run.cmd` | `1ef83cd7feb9362c57945a950dd227a11aa709dc2eb828307fed934cdcb25cef` |
| `lean-toolchain` | `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b` |

Original FIX3 ZIP SHA-256: `51a08514472acae3a3d9c5de5db06b4c146171ac5577ab54733bcb67a81fcc48`.

Original FIX3 manifest SHA-256: `40f58256c3932ec193dd56b1fa5c49e1ccee749479600c3582418286443c8d8f`.

All 25 entries of the retained original manifest match the retained FIX3 package. The five Lean files, native runner and toolchain declaration published here are byte-identical to that package. This publication's `sources.sha256` is regenerated for the AIM939 directory. Documentation changes and removal of unrelated baseline records do not change any proof source, theorem statement, audit, runner or allowed axiom.

## Inspected external transcript

The user supplied a native Windows execution transcript identifying Lean `4.33.0`, target `x86_64-w64-windows-gnu`, Release, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.

The transcript reports:

```text
COMPILE_PASS=AIM939\Core.lean
COMPILE_PASS=AIM939\Diagonal.lean
COMPILE_PASS=AIM939\FiniteWitness.lean
COMPILE_PASS=AIM939_COUNTEREXAMPLE.lean
```

It displays the existential counterexample signature and the exact negative root. Each of the 12 targets in [audit-theorems.txt](../audit-theorems.txt) has an `AXIOM_AUDIT_PASS` marker with exactly `[propext, Classical.choice, Quot.sound]`. The final lines include:

```text
AXIOM_AUDIT_PASS=AIM939.AIM939_COUNTEREXAMPLE; AXIOMS=[propext, Classical.choice, Quot.sound]
AIM939_THEOREM_AUDIT=PASS_STANDARD_ONLY
AIM939_NATIVE_RESULT=PASS
```

These excerpts summarize the supplied evidence. This file is not a raw compiler log. `Audit.lean` verifies that each target is a theorem declaration and rejects every transitive axiom outside the three-name allowlist, including `sorryAx`.

## Acceptance and completeness

The received execution evidence is the user-supplied FIX3 transcript. The full raw external evidence directory, external `source-hashes.log` and compiled objects were not separately uploaded or inspected. The unchanged original runner can report its final PASS only after compiler-version verification, every source-manifest check, all four successful compilations, successful audit execution and the expected audit marker. Successful source gating is consequently inferred from that control flow and the matching fixed package; it is not asserted as an independently inspected external hash log.

The retained source identities and transcript establish the accepted exact root status. Historical candidate comments in the source remain byte-identical; this record supplies their subsequent accepted status. No local Lean/Lake run or new publication-time compiler execution occurred.

The reference Mathlib API revision is `db584cd6d46c92f209a44c0f1c829460d327499d`. This is not a measured Git identity of the external dependency cache. New reproductions require a compatible existing cache.

The exact negative root has no unresolved certificate, witness, checker, admission, semantic or analytic obligation. The frozen universal source implication is mathematically refuted because it includes this `n = p = 4` instance. The formal root remains the explicitly defined four-variable negation. The source-to-target correspondence is documented in [AIM939_SOURCE_SCOPE.txt](../AIM939_SOURCE_SCOPE.txt).

Historical priority, human peer review, public AIM catalogue admission and a catalogue-specific Linux-verifier pass are not established by this evidence. Raw personal filesystem paths, dependency caches and generated compiler objects are excluded from publication.
