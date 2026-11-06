# AIM025 — exact complex Hermitian PSD formalization candidate

```text
PACKAGE=AIM025_EXACT_FORMALIZATION_433_v0_1_0
MODE=A_TIER_DERIVATION
NEW_SOURCE_STATUS=A_TIER_CANDIDATE
EXACT_TARGET_STATEMENT=DEFINED
UNRESTRICTED_TARGET_PROOF=NOT_SUPPLIED
ORIGINAL_AIM025_CLOSURE=OPEN
LOCAL_LEAN_LAKE_EXECUTIONS=0
```

## Exact target

[Original statement, pinned revision](https://github.com/MColbrook/AIM/blob/4f5b1659355cb61d194da94ef14615214e1363a8/problems/025-chollet-permanent.md).

For every integer $n\ge 1$ and every pair of complex Hermitian positive
semidefinite matrices $A,B\in M_n(\mathbb C)$,

$$
\operatorname{per}(A\circ B)\le
\operatorname{per}(A)\operatorname{per}(B).
$$

The native permanent is unnormalized. The Hadamard product is entrywise
multiplication. The target imposes no entrywise sign, zero-imaginary-part,
rank, or factorization hypothesis.

```lean
open scoped ComplexOrder

def CholletFor (A B : Matrix ι ι ℂ) : Prop :=
  Matrix.permanent (Matrix.hadamard A B) ≤
    Matrix.permanent A * Matrix.permanent B

def CholletAt (n : ℕ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A.PosSemidef → B.PosSemidef → CholletFor A B

def CholletConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → CholletAt n
```

Namespace: `AIM025.Exact`. The first definition has implicit
`{ι : Type*} [Fintype ι] [DecidableEq ι]`.

**A definition of the target proposition is not a proof of that proposition.**
The package contains no unconditional theorem of type `CholletConjecture`.

## Candidate theorem content

| Component | Exact content | Source status |
| --- | --- | --- |
| Existing core | Finite entrywise nonnegative real inequality, residual, equality and normalization results | Accepted baseline source; byte-identical copy |
| Exact target | Native complex PSD conjecture; Hermitian-permanent reality; equivalence with the real residual; exact counterexample criterion | `A_TIER_CANDIDATE` |
| Transfer | Real-to-complex permanent and Hadamard compatibility; original inequality on the real, nonnegative entry subclass | `A_TIER_CANDIDATE` |
| Audit | 36 baseline + 12 exact-target + 9 transfer theorem declarations | Prepared; 57 external audits required |

For Hermitian matrices, the prepared reality lemmas establish that all
permanents in the comparison are real. The native `ComplexOrder` relation
therefore agrees with the ordinary real inequality.

Define

$$
\Delta(A,B)=
\Re\operatorname{per}(A)\,\Re\operatorname{per}(B)
-\Re\operatorname{per}(A\circ B).
$$

The prepared theorems establish

$$
\operatorname{CholletFor}(A,B)\iff\Delta(A,B)\ge0
$$

under Hermitian hypotheses, and

$$
\neg\operatorname{CholletConjecture}
\iff
\exists n\ge1,\;A,B\text{ native PSD},\;\Delta(A,B)<0.
$$

No negative-residual witness is supplied.

## Restricted root

`AIM025.Exact.AIM025_CHOLLET_PSD_REAL_NONNEGATIVE` assumes native
`A.PosSemidef` and `B.PosSemidef`, together with

```lean
hAim : ∀ i j, (A i j).im = 0
hBim : ∀ i j, (B i j).im = 0
hAre : ∀ i j, 0 ≤ (A i j).re
hBre : ∀ i j, 0 ≤ (B i j).re
```

and concludes

```lean
CholletFor A B ∧ 0 ≤ cholletGap A B
```

The additional entry hypotheses remain explicit. Positive semidefiniteness
alone has not been shown to imply the target.

## Files

| File | Content |
| --- | --- |
| [AIM025Exact.lean](AIM025Exact.lean) | Exact statement and 12 semantic/residual/counterexample theorems |
| [AIM025Bridge.lean](AIM025Bridge.lean) | 9 transfer and restricted-root theorems |
| [AIM025CholletNonnegative.lean](AIM025CholletNonnegative.lean) | Unchanged accepted baseline |
| [AIM025_EXACT_FORMALIZATION_A_TIER.txt](AIM025_EXACT_FORMALIZATION_A_TIER.txt) | Endpoint, mathematical justification, status and unresolved obligations |
| [Audit.lean](Audit.lean) | Full signatures, axiom reports and standard-only allowlist gate |
| [audit-theorems.txt](audit-theorems.txt) | Exact 57-target list |
| [modules.txt](modules.txt) | Deterministic compilation order |
| [run.cmd](run.cmd) | Cached native Windows compilation and evidence capture |
| [package.json](package.json) | Machine-readable scope and evidence status |
| [SHA256SUMS](SHA256SUMS) | Package file integrity |
| [provenance/SOURCES.md](provenance/SOURCES.md) | Pinned source references |
| [provenance/BASELINE_VERIFICATION.md](provenance/BASELINE_VERIFICATION.md) | Prior accepted core evidence boundary |

## Cached native Windows execution

Compiler: native Lean **4.33.0**, Windows GNU target, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`.

Required installation:
`%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe`.

Default existing cache project:
`%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1`.

Save the supplied ZIP in Downloads. Execute in Windows CMD:

```bat
cd /d "%USERPROFILE%\Downloads" && tar -xf "AIM025_EXACT_FORMALIZATION_433_v0_1_0.zip" && call "AIM025_EXACT_FORMALIZATION_433_v0_1_0\run.cmd"
```

A different existing compatible cache project or Mathlib root can be supplied
as the first argument to `run.cmd`.

The runner verifies source hashes and native compiler identity, reuses cached
dependencies, compiles the three package modules into a fresh evidence
directory, and compiles the audit. It requires all 57 theorem reports and
rejects every transitive axiom outside `propext`, `Classical.choice`,
and `Quot.sound`. Dependency acquisition and rebuilding are disabled.

The evidence directory contains source snapshots, compiler logs, theorem
reports, and small dependency identity records. Available cached manifests
and optional Git checkout metadata support external review. No complete
dependency-object hash census is performed; existing cache source/object
correspondence is trusted. Native `tar.exe`, when available, also produces
an evidence ZIP.

## Promotion boundary

```text
STATIC_SOURCE_REVIEW=COMPLETED
LOCAL_COMPILER_RUN=NONE
NEW_EXTERNAL_COMPILER_RESULT=ABSENT
NEW_THEOREM_AXIOM_AUDIT_RESULT=ABSENT
A_TIER_PROMOTION=REVIEW_REQUIRED
ORIGINAL_AIM025_CLOSURE=OPEN
```

A successful external run can validate the 57 listed theorem declarations.
It cannot supply the missing proof of `CholletConjecture`. The unresolved
universal residual obligation is recorded as `PSDResidualNonnegative`;
its equivalence to the conjecture introduces no independent certificate.

