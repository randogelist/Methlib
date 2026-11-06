# Initial external run and FIX1

```text
INITIAL_PACKAGE=AIM025_EXACT_FORMALIZATION_433_v0_1_0
CURRENT_PACKAGE=AIM025_EXACT_FORMALIZATION_433_v0_1_0_FIX1
EVIDENCE_BASIS=USER_SUPPLIED_CONSOLE_TRANSCRIPT
EVIDENCE_ZIP_INSPECTED=FALSE
LOCAL_LEAN_LAKE_EXECUTIONS=0
```

## Matched source identity

| Item | SHA-256 |
| --- | --- |
| Initial source manifest | `a7fa722ae8f178a44cb2b91b15ed6ab439b691a850247a19b8d35c3e9d65ae91` |
| Unchanged core | `8d6371fb72c496f43400bb93ba73a9df96c9e1cdac3b9aa35b384197d47acd17` |
| Unchanged exact-target module | `0b361a488cfb6e17f2e26cac8ac9bc5e6666611be7a5d2c52eac7cb9a479c25f` |
| Initial bridge | `83e55f70d3c587ff2739aa4bc800cf8b52cd69eac731b2a1c1e370e8645b2812` |
| Unchanged audit | `94f84ae4447134c0b2cfffe5c919927b5e7ef059079a0b81afad7ebf8d4676e5` |

The transcript reports the source-manifest, core, and audit hashes and a
successful source-snapshot gate. The exact-target and initial-bridge hashes
above are recovered from that matching manifest and verified against the
retained initial package.

## Supplied external result

```text
COMPILER_VERSION=4.33.0
COMPILER_TARGET=x86_64-w64-windows-gnu
COMPILER_COMMIT=d8b18978322de05a8f3dba51ef03cf5461676c17
SOURCE_SNAPSHOT_HASHES=PASS
NATIVE_EXIT=AIM025CholletNonnegative.lean:0
NATIVE_EXIT=AIM025Exact.lean:0
NATIVE_EXIT=AIM025Bridge.lean:1
FINAL_EXIT=1
THEOREM_AXIOM_AUDIT=NOT_REACHED
```

The core's unused-section-variable messages are linter warnings. The core
and exact-target module both returned compiler exit 0.

The first bridge error occurs in the statement of `permanent_complexify`.
The expected complex result in `(Matrix.permanent A : ℂ)` constrains the
polymorphic permanent to complex matrices, although `A` is a real matrix.
The later references to the undeclared theorem therefore fail.

## Source correction

```diff
- Matrix.permanent (complexify A) = (Matrix.permanent A : ℂ) := by
+ Matrix.permanent (complexify A) = Complex.ofReal (Matrix.permanent A) := by
```

Since `Complex.ofReal : ℝ → ℂ`, its argument fixes the permanent's scalar
type to `ℝ`. The theorem's intended mathematical content is unchanged.
The proof body and all dependent theorem declarations remain unchanged.

## Runner correction

At module and audit compilation, the runner now returns on nonzero compiler
exit before checking object-file existence. A compilation error therefore
retains its primary diagnosis. A zero compiler exit with a missing output
object remains a separate failure.

## Acceptance boundary

```text
EXACT_TARGET_MODULE_COMPILATION=PASS_PRIOR_MATCHING_SOURCE
EXACT_TARGET_THEOREM_AXIOM_AUDIT=PENDING
FIX1_BRIDGE_COMPILATION=PENDING
ALL_57_THEOREM_AXIOM_AUDITS=PENDING
NEW_THEOREM_STATUS=A_TIER_CANDIDATE
ORIGINAL_AIM025_CLOSURE=OPEN
```

The initial transcript supplies no audit result for the 21 new declarations.
Neither the initial partial run nor the FIX1 source correction establishes
A-tier promotion. Full matching external compilation and the 57-target
standard-only audit remain required.

