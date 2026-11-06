# Pinned sources

## Original target

- Repository: `MColbrook/AIM`.
- Commit: `4f5b1659355cb61d194da94ef14615214e1363a8`.
- Path: `problems/025-chollet-permanent.md`.
- Blob: `5c9eb64e2b6472f1f926996576059b008c633fdf`.
- [Pinned statement](https://github.com/MColbrook/AIM/blob/4f5b1659355cb61d194da94ef14615214e1363a8/problems/025-chollet-permanent.md).
- [Source snapshot](ORIGINAL_AIM025.md).

The upstream snapshot supplies the exact problem statement. Its literature
status is an upstream report, not an independent certification of current
global resolution status.

## Accepted restricted baseline

- Repository: `randogelist/Methlib`.
- Commit: `dacf8ea7e5574df25b99dbcb89e8eb531311fb8f`.
- [Core](https://github.com/randogelist/Methlib/blob/dacf8ea7e5574df25b99dbcb89e8eb531311fb8f/AIM_LEAN_SNIPES/AIM025/AIM025CholletNonnegative.lean).
- Core SHA-256: `8d6371fb72c496f43400bb93ba73a9df96c9e1cdac3b9aa35b384197d47acd17`.
- [Published evidence record](https://github.com/randogelist/Methlib/blob/dacf8ea7e5574df25b99dbcb89e8eb531311fb8f/AIM_LEAN_SNIPES/AIM025/evidence/VERIFICATION.md).
- [Evidence-record snapshot](BASELINE_VERIFICATION.md).

The baseline acceptance covers its finite entrywise nonnegative real scope.
No new-source acceptance is inferred from the baseline acceptance.

## Mathlib source API reference

Commit: `db584cd6d46c92f209a44c0f1c829460d327499d`.

- [Native permanent](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Permanent.lean).
- [Native positive semidefiniteness](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/PosDef.lean).
- [Hermitian matrices](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Hermitian.lean).
- [Complex real-axis order](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Complex/Order.lean).
- [Complex ring homomorphism](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Complex/Basic.lean).
- [Conjugation of finite sums and products](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Star/BigOperators.lean).

## External compiler

```text
VERSION=4.33.0
TARGET=x86_64-w64-windows-gnu
COMMIT=d8b18978322de05a8f3dba51ef03cf5461676c17
```

Source inspection establishes API expectations. External compilation and
the theorem-level axiom audit remain required.

