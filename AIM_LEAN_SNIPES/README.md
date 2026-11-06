# AIM_LEAN_SNIPES

## Instructions for agents

```text
PROJECT=conjecture_bonetooth
WORKFLOW=YOU_ARE_GOODWORKFLOWFRONTIER
APPLIES_TO=AIM_LEAN_SNIPES/**
MODES=DISCUSSION | B_TIER_DERIVATION | A_TIER_DERIVATION
LOCAL_LEAN_EXECUTION=PROHIBITED
DEPENDENCIES=EXISTING_COMPATIBLE_CACHE_ONLY
```

Read and preserve this workflow before creating or modifying a problem entry.
The user's explicit instructions and existing authorization govern the task.

## 1. Directory convention

- Keep `AIM_LEAN_SNIPES/` as the collection root.
- Use one direct child directory per exact upstream AIM identifier:
  `AIM_LEAN_SNIPES/AIM025/`, then `AIM_LEAN_SNIPES/AIM<identifier>/`
  for subsequent requested problems. Preserve the identifier and its padding.
- Keep each problem's sources, derivations, audit, native runner, toolchain
  declaration, status record and evidence references inside its own directory.
- Create a new problem directory when its requested material exists. Do not
  precreate empty candidate folders or add unrelated projects.
- Keep the collection root limited to this README and problem directories.
  This README also prevents GitHub from compacting the sole child path.
- Preserve existing accepted filenames and source bytes during organization.
  Multiple scoped endpoints of one problem remain within that problem's directory.

## 2. Freeze the mathematical endpoint

Before derivation or formalization, record:

```text
AIM_ID
ORIGINAL_PROBLEM_SOURCE_AND_REVISION
ROOT_THEOREM
EXACT_QUANTIFIERS_AND_PREMISES
EXACT_CONCLUSION
SCOPED_STATUS
ORIGINAL_PROBLEM_CLOSURE
UNRESOLVED_OBLIGATIONS
```

State the exact relationship between the selected endpoint and the original
conjecture. A restricted class, conditional implication, certificate theorem or
counterexample must be labeled by its actual scope. Keep original-problem
closure separate from closure of a derived endpoint. Kernel acceptance alone
does not establish novelty.

## 3. Required artifacts by mode

| Mode | Required result |
| --- | --- |
| `DISCUSSION` | Conversation only; no TXT or formal artifact solely for discussion. |
| `B_TIER_DERIVATION` | Complete mathematical derivation of the exact endpoint in `<THEOREM>_B_TIER.txt`. |
| `A_TIER_DERIVATION` | Lean source `<THEOREM>.lean`, `<THEOREM>_A_TIER.txt`, `run.cmd`, and theorem-level audit support. |

An A-tier problem directory also records the selected toolchain, exact audited
target list, reproduction instructions and external evidence basis. Additional
Lean modules are permitted when required by the proof. Keep all local proof
sources together; dependencies may come from the declared external cache.

When a runnable package is requested, provide exactly one ZIP and one copyable
Windows extraction/run command, with direct download links.

## 4. Lean construction and cached native execution

- Never execute Lean or Lake in the agent environment, including compiler
  version or help probes. `run.cmd` is for the user's external native Windows
  compiler.
- Respect the problem's declared compiler and compatible cache. The established
  toolchains are Lean `4.33.0` or `4.34.0-rc1`, according to the selected
  package and task context. Do not silently upgrade.
- Reuse existing compiled dependencies. Disable dependency acquisition and
  dependency rebuilding. Compile the requested proof modules and audit against
  that cache; stale candidate objects do not establish a changed source.
- When safe, use explicit endpoint signatures, independent opaque edge theorems,
  native asynchronous elaboration and a deterministic final chain.
- Scheduling changes may not change the theorem, premises, permitted axioms or
  endpoint. Pending signatures remain unproved until their bodies pass the
  external Lean kernel.
- Require successful native compilation and a theorem-level axiom audit for
  every claimed accepted target. Reject `sorryAx` and unapproved axioms.
  The established standard allowlist is `propext`, `Classical.choice` and
  `Quot.sound`; do not silently extend it.

## 5. Evidence and promotion

Prepared code without matching external compiler and theorem-level audit
evidence has status `A_TIER_CANDIDATE`. Only matching successful external
evidence can promote the exact source and theorem to `A_TIER`.

Record the compiler identity, source identity, compilation outcome, audited
target coverage and permitted axiom dependencies. Use source matching sufficient
to establish that the evidence belongs to the published theorem. Preserve
existing required source manifests and update them when their covered files
change.

Distinguish inspected logs, user-supplied excerpts and uninspected evidence
archives. State the actual acceptance basis and any evidence limitation.
An uninspected archive is not an inspected pass. Do not claim a new compiler
run when only documentation or repository layout changed.

Retain accepted status when the audited source remains unchanged and its
accepted evidence remains applicable. Changed proof sources or statements
require matching evidence before renewed promotion. Keep personal filesystem
paths, credentials, dependency caches and generated compiler objects out of
public publication; use relative references and evidence summaries.

## 6. Status definitions

| Status | Exact criterion |
| --- | --- |
| `B_TIER` | Complete mathematical derivation of the exact theorem recorded in its TXT. |
| `A_TIER_CANDIDATE` | Prepared Lean source without matching successful external compiler and theorem-level audit evidence. |
| `A_TIER` | Exact Lean theorem passed the external compiler and theorem-level axiom audit without `sorryAx` or unapproved axioms. |
| `FORMAL_CLOSURE` | Exact implication from all explicitly stated premises to the scoped root conclusion is A-tier. Certificates, witnesses or admissions may remain explicitly unresolved. |
| `CONDITIONAL_FORMAL_CLOSURE` | Formal closure with named unresolved certificate, witness, checker, admission, semantic or analytic premises. |
| `UNCONDITIONAL_CLOSURE` | Exact scoped root is A-tier and every certificate, witness, checker endpoint, admission, semantic or analytic obligation within that scope is discharged. |

```text
!=B_TIER
!!=A_TIER
!!!=FORMAL_CLOSURE
!!!!=UNCONDITIONAL_CLOSURE
```

Apply each marker only to its explicitly recorded endpoint. Ordinary quantified
hypotheses define the theorem's domain; unresolved construction or analytic
obligations must not be hidden as discharged premises.

## 7. Repository publication

- Publish only the requested problem entry and necessary collection documentation.
- Preserve other entries and concurrent repository changes. Use atomic commits
  based on the current branch head, with an expected-head check; never force an
  overwrite of concurrent work.
- Verify the published paths and source identity by readback.
- Add or modify CI only when requested or already authorized.
- Report the directory, commit and actual verification status using direct links.

## Current entries

| Directory | Exact scope | Recorded status |
| --- | --- | --- |
| [AIM025](AIM025/) | Finite entrywise nonnegative real matrices: permanent residual, inequality, equality classification and normalized overlap. | `!!!!` for the scoped endpoint; unrestricted complex Hermitian PSD AIM025 is not closed by this result. |

AIM025's accepted source and external verification basis are recorded in its
[README](AIM025/README.md) and
[verification record](AIM025/evidence/VERIFICATION.md).

