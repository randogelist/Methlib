#!/usr/bin/env bash
set -euo pipefail

ATTEMPT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ROOT="$(cd "$ATTEMPT/../../.." && pwd)"
OPENAI="$ROOT/.ci-openai/lean"
REF="$ROOT/.ci-referee/970/openai-jacobsthal-quadratic-refereed/bridge687"
EVIDENCE="$ATTEMPT/evidence/${GITHUB_RUN_ID:-manual}-${GITHUB_RUN_ATTEMPT:-0}"
mkdir -p "$EVIDENCE"

OAI_SHA=1581d4cbdd69a0faf34b2089614fe2a814316a6a
REF_SHA=634b667ee7844f12590117c4c2d7bc0143f2fdd9
BRIDGE_BLOB=64a1cf3ff88a4f655ae7284aa3fb99ed9eab4932
MATHLIB_SHA=d13f23b723b8a846827a245b89c10fc7d3f11612

test "$(git -C "$ROOT/.ci-openai" rev-parse HEAD)" = "$OAI_SHA"
test "$(git -C "$ROOT/.ci-referee" rev-parse HEAD)" = "$REF_SHA"
test "$(git hash-object "$REF/Bridge687.lean")" = "$BRIDGE_BLOB"
test "$(cat "$OPENAI/lean-toolchain")" = 'leanprover/lean4:v4.34.1'
if grep -En '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' "$ATTEMPT/FiniteCore.lean" "$ATTEMPT/ExternalRoot.lean"; then
  echo "LOCAL_AXIOM_OR_HOLE=FAIL" >&2; exit 1
fi

cd "$OPENAI"
lean --version | tee "$EVIDENCE/lean-version.log"
printf '%s\n' "$OAI_SHA" > "$EVIDENCE/openai-commit.txt"
printf '%s\n' "$REF_SHA" > "$EVIDENCE/referee-commit.txt"
lake update 2>&1 | tee "$EVIDENCE/lake-update.log"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$MATHLIB_SHA"
lake exe cache get 2>&1 | tee "$EVIDENCE/mathlib-cache.log"
test -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean || lake -j1 build Mathlib
printf '%s\n' "$MATHLIB_SHA" > "$EVIDENCE/mathlib-commit.txt"

# First prove the independent finite certificate (cached Mathlib only).
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -o "$1/FiniteCore.olean" "$1/FiniteCore.lean"' _ "$ATTEMPT" 2>&1 | tee "$EVIDENCE/finite-core-build.log"

# Then compile the actual pinned external theorem and formal #687 bridge.
lake -j1 build OAI.NumberTheory.Jacobsthal.Main 2>&1 | tee "$EVIDENCE/jacobsthal-build.log"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -o "$1/Bridge687.olean" "$1/Bridge687.lean"' _ "$REF" 2>&1 | tee "$EVIDENCE/external-bridge-build.log"
lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; lean -o "$1/ExternalRoot.olean" "$1/ExternalRoot.lean"' _ "$ATTEMPT" "$REF" 2>&1 | tee "$EVIDENCE/external-root-build.log"

lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; lean --trust=0 "$1/Audit.lean"' _ "$ATTEMPT" "$REF" 2>&1 | tee "$EVIDENCE/axiom-audit.log"

python3 - "$EVIDENCE/axiom-audit.log" <<'PY'
import re, sys
log=open(sys.argv[1], encoding="utf-8").read()
names=[
"MethlibErdos687.AttemptF.survivor_pos_iff",
"MethlibErdos687.AttemptF.two_blocks",
"MethlibErdos687.AttemptF.moment_strict_forces_all_positive",
"MethlibErdos687.AttemptF.moment_certificate_sound",
"MethlibErdos687.AttemptF.moment_certificate_accepted",
"MethlibErdos687.AttemptF.certificate_excludes_cover",
"MethlibErdos687.AttemptF.external_part_ii",
"MethlibErdos687.AttemptF.external_quantitative",
"MethlibErdos687.AttemptF.external_two_blocks",
"MethlibErdos687.AttemptF.external_plus_certificate",
]
approved={"propext","Classical.choice","Quot.sound"}
for name in names:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]", log)
    if m:
        axs={a.strip() for a in m.group(1).split(",") if a.strip()}
    elif re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", log):
        axs=set()
    else:
        raise SystemExit("THEOREM_AXIOM_AUDIT=MISSING|"+name)
    if not axs <= approved:
        raise SystemExit("THEOREM_AXIOM_AUDIT=FAIL|"+name+"|"+repr(sorted(axs)))
    print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|"+name+"|"+",".join(sorted(axs)))
PY

echo "FINITE_BKQR_AND_EXTERNAL_ROOT=PASS" | tee "$EVIDENCE/final-status.txt"
echo "NEAR_LINEAR_ERDOS_687=NOT_PROVED" | tee -a "$EVIDENCE/final-status.txt"
if test -n "${GITHUB_STEP_SUMMARY:-}"; then
  { echo "### Erdős #687 / Attempt_F"; echo "Finite BKQR + external source + theorem-level audit: PASS"; echo "Near-linear bound: OPEN"; } >> "$GITHUB_STEP_SUMMARY"
fi
