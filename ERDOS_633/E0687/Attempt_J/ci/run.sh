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

cd "$OPENAI"
lean --version | tee "$EVIDENCE/lean-version.log"
echo "$OAI_SHA" > "$EVIDENCE/openai-commit.txt"
echo "$REF_SHA" > "$EVIDENCE/referee-commit.txt"
git -C "$ROOT" rev-parse HEAD > "$EVIDENCE/methlib-commit.txt"
sha256sum "$ATTEMPT/Erdos687AttemptJ.lean" "$ATTEMPT/Audit.lean" > "$EVIDENCE/source.sha256"

# Official cached Mathlib oleans; build the exact external theorem DAG only.
lake update 2>&1 | tee "$EVIDENCE/lake-update.log"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$MATHLIB_SHA"
lake exe cache get 2>&1 | tee "$EVIDENCE/mathlib-cache.log"
test -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean || lake -j1 build Mathlib
echo "$MATHLIB_SHA" > "$EVIDENCE/mathlib-commit.txt"

lake -j1 build OAI.NumberTheory.Jacobsthal.Main 2>&1 | tee "$EVIDENCE/jacobsthal-build.log"

# Recompile the original external covering bridge without modifications.
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --trust=0 -o "$1/Bridge687.olean" "$1/Bridge687.lean"' _ "$REF" 2>&1 | tee "$EVIDENCE/external-bridge-build.log"
lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; lean --trust=0 -o "$1/Erdos687AttemptJ.olean" "$1/Erdos687AttemptJ.lean"' _ "$ATTEMPT" "$REF" 2>&1 | tee "$EVIDENCE/methlib-root-build.log"
lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; lean --trust=0 "$1/Audit.lean"' _ "$ATTEMPT" "$REF" 2>&1 | tee "$EVIDENCE/axiom-audit.log"

python3 - "$EVIDENCE/axiom-audit.log" <<'PY'
import re, sys
log = open(sys.argv[1], encoding="utf-8").read()
names = [
    "MethlibErdos687.AttemptJ.pairCount_pos_iff",
    "MethlibErdos687.AttemptJ.pairCount_pos_iff_universal",
    "MethlibErdos687.AttemptJ.noCover_insert_iff_gram",
    "MethlibErdos687.AttemptJ.noCover_primes_of_jacobsthal",
    "MethlibErdos687.AttemptJ.gram_of_jacobsthal",
    "MethlibErdos687.AttemptJ.quadratic_uniform_gram",
    "MethlibErdos687.AttemptJ.erdos_687_part_ii",
    "MethlibErdos687.AttemptJ.erdos_687_quantitative",
    "Erdos687.lt_of_covered",
    "Erdos687.Y_isBigO",
    "Erdos687.erdos_687.parts.ii",
    "OAI.Erdos970.Erdos970Final.erdos_970_quadratic",
]
approved = {"propext", "Classical.choice", "Quot.sound"}
if "sorryAx" in log:
    raise SystemExit("THEOREM_AXIOM_AUDIT=FAIL_SORRYAX")
for name in names:
    p = r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]"
    m = re.search(p, log)
    if m is None:
        if re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", log):
            print("THEOREM_AXIOM_AUDIT=PASS_NO_AXIOMS|" + name)
            continue
        raise SystemExit("THEOREM_AXIOM_AUDIT=MISSING|" + name)
    axioms = {x.strip() for x in m.group(1).split(",") if x.strip()}
    if not axioms <= approved:
        raise SystemExit("THEOREM_AXIOM_AUDIT=FAIL|" + name + "|" + repr(sorted(axioms)))
    print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|" + name + "|" + ",".join(sorted(axioms)))
PY

printf '%s\n' 'DAG_COMPILE=PASS' 'AXIOM_AUDIT=PASS_STANDARD_ONLY' 'FORMAL_CLOSURE=PART_II_AND_QUADRATIC_GRAM' 'STRONG_ERDOS_687_ENDPOINT=NOT_PROVED' | tee "$EVIDENCE/final-status.txt"
if test -n "${GITHUB_STEP_SUMMARY:-}"; then
  {
    echo "### Erdős #687 / Attempt_J"
    echo "DAG_COMPILE=PASS"
    echo "AXIOM_AUDIT=PASS_STANDARD_ONLY"
    echo "FORMAL_CLOSURE=PART_II_AND_QUADRATIC_GRAM"
    echo "STRONG_ERDOS_687_ENDPOINT=NOT_PROVED"
  } >> "$GITHUB_STEP_SUMMARY"
fi
