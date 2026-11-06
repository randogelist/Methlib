# Pinned source and API provenance

## Problem statement

- [AIM025: Chollet permanent conjecture, pinned AIM commit](https://github.com/MColbrook/AIM/blob/4f5b1659355cb61d194da94ef14615214e1363a8/problems/025-chollet-permanent.md).
- AIM reference commit: `4f5b1659355cb61d194da94ef14615214e1363a8`.
- Scope of this repository entry: finite real matrices with entrywise nonnegative entries. The original complex Hermitian PSD target is not established by this scoped result.

## Native matrix APIs

- [Mathlib permanent](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Permanent.lean).
- [Mathlib Hadamard product](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Hadamard.lean).
- Reference Mathlib commit: `db584cd6d46c92f209a44c0f1c829460d327499d`.

The formal root uses native `Matrix.permanent` and `Matrix.hadamard`. The source calibrates its row-permutation products against the native permanent convention using transpose invariance.

## Native theorem-level audit

- [Lean `collectAxioms`](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Lean/Util/CollectAxioms.lean).
- [Lean print commands](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Lean/Elab/Print.lean).
- [Lean command evaluation](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Lean/Elab/BuiltinEvalCommand.lean).
- Native Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`.

`Audit.lean` combines native `#check`, native `#print axioms` and a `Lean.collectAxioms` allowlist guard for the exact 36 names in `audit-theorems.txt`. Missing declarations, a target-count mismatch or any unapproved axiom cause audit failure. Explicit theorem signatures and `set_option Elab.async true` preserve the proof endpoint; asynchronous signatures alone do not establish proof completion.

## Mathematical source record

[AIM025_CHOLLET_HVR_SUBCLASS_B_TIER.txt](AIM025_CHOLLET_HVR_SUBCLASS_B_TIER.txt) is retained unchanged as historical mathematical provenance.

```text
SHA256=786f287dd4307099204450a82277b607f3bc362136c6a781f35a2977687cf7dd
```

Its broader PSD equality and operator/HVR endpoints are not included in the accepted Lean root. Its historical `A_TIER_CLAIM=NONE` describes that source record. The accepted finite scope is specified by `../AIM025_CHOLLET_NONNEGATIVE_A_TIER.txt`; its complete finite derivation is `../AIM025_CHOLLET_NONNEGATIVE_B_TIER.txt`.
