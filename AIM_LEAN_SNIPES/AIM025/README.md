# AIM025 — finite entrywise nonnegative matrices

**Status: `!!!! UNCONDITIONAL_CLOSURE` for the exact finite nonnegative scope.**

| Field | Value |
| --- | --- |
| Root theorem | `AIM025.AIM025_CHOLLET_NONNEGATIVE` |
| Accepted formal status | `A_TIER` |
| Theorem-level axiom audit | 36 / 36, standard axioms only |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Unresolved obligations within the formalized scope | 0 |
| Native compiler | Lean 4.33.0, `x86_64-w64-windows-gnu` |
| Full original complex Hermitian PSD AIM025 | Unresolved by this result |

## Exact scope

For every finite type `n` and real matrices `A B : Matrix n n ℝ`, the hypotheses are

```lean
hA : ∀ i j, 0 ≤ A i j
hB : ∀ i j, 0 ≤ B i j
```

With `aσ = ∏ i, A i (σ i)` and `bτ = ∏ i, B i (τ i)`, the accepted root establishes

$$
\operatorname{per}(A)\operatorname{per}(B)-\operatorname{per}(A\circ B)
=\sum_{\sigma\ne\tau}a_\sigma b_\tau\ge0.
$$

Equality holds exactly when either permanent is zero or the two permutation-weight families have the same unique positive support. Under positive-permanent antecedents, normalized permutation distributions have mass one; the normalized Hadamard permanent is their overlap, the normalized residual is one minus that overlap, and overlap equals one exactly for common singleton support. The empty index type is included. Finite nonnegative weighted-Gram specializations are also audited.

Entrywise nonnegativity is an explicit hypothesis. Positive semidefiniteness is not required for this scoped result. The unrestricted complex Hermitian positive-semidefinite AIM025 conjecture and the broader operator/HVR endpoints are outside this formalized scope. No novelty claim is asserted.

## Files

| File | Content |
| --- | --- |
| [AIM025CholletNonnegative.lean](AIM025CholletNonnegative.lean) | Accepted definitions, 36 theorem targets and root theorem |
| [Audit.lean](Audit.lean) | Native signatures, axiom reports and `Lean.collectAxioms` allowlist guard |
| [AIM025_CHOLLET_NONNEGATIVE_B_TIER.txt](AIM025_CHOLLET_NONNEGATIVE_B_TIER.txt) | Complete finite mathematical derivation |
| [AIM025_CHOLLET_NONNEGATIVE_A_TIER.txt](AIM025_CHOLLET_NONNEGATIVE_A_TIER.txt) | Accepted scope, exact root signature and closure record |
| [evidence/VERIFICATION.md](evidence/VERIFICATION.md) | External evidence summary and completeness statement |
| [run.cmd](run.cmd) | Native cached Windows reproduction and evidence capture |
| [package.json](package.json) | Source identities, scope and machine-readable status |
| [audit-theorems.txt](audit-theorems.txt) | Exact 36-target audit list |
| [SHA256SUMS](SHA256SUMS) | Publication file-integrity manifest |
| [provenance/SOURCES.md](provenance/SOURCES.md) | Pinned problem and API references |

## Cached native Windows reproduction

Requirements: the existing native Lean 4.33.0 installation at `%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe` and a compatible, already compiled Mathlib cache. The default cache project is `%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1`. Dependency acquisition and dependency rebuilding are disabled.

From the repository root, in Windows CMD:

```bat
call "AIM_LEAN_SNIPES\AIM025\run.cmd"
```

An existing compatible cache project or Mathlib root can be supplied as the first argument:

```bat
call "AIM_LEAN_SNIPES\AIM025\run.cmd" "D:\existing-cached-project"
```

The runner snapshots and verifies `SHA256SUMS`, checks the pinned native compiler identity, compiles the core and audit against cached dependencies, and requires all 36 theorem audits. Fresh outputs are written beneath `evidence/r-*`; optional native `tar.exe` creates a corresponding evidence ZIP. Generated run evidence and object files are excluded by the local `.gitignore`.

The runner retains its audited package label `AIM025_CHOLLET_NONNEGATIVE_433_FIX3`. Its `A_TIER_PROMOTION=REVIEW_REQUIRED` marker applies to a newly produced run record. The prior accepted source status is recorded separately in the acceptance record. `.gitattributes` preserves the accepted source bytes and the native CMD line endings during checkout.

## Evidence boundary

Acceptance uses reviewed user-supplied external Windows output: the FIX2 core transcript, identical FIX3 core source, the successful FIX3 completion excerpt, and the known runner's source/compiler/audit gates. The complete FIX3 evidence ZIP was not uploaded or inspected. Raw transcripts and personal filesystem paths are omitted from publication. No local Lean/Lake execution or new publication-time compiler run is claimed. See [VERIFICATION.md](evidence/VERIFICATION.md).
