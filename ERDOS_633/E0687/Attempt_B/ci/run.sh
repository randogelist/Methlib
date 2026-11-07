#!/usr/bin/env bash
set -euo pipefail

ATTEMPT="$(cd "$(dirname "$0")/.." && pwd)"
ROOT="$(cd "$ATTEMPT/../../.." && pwd)"
OPENAI="$ROOT/.ci-openai/lean"
REF="$ROOT/.ci-referee/970/openai-jacobsthal-quadratic-refereed/bridge687"
EVIDENCE="$ATTEMPT/evidence/$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT"
mkdir -p "$EVIDENCE"

OAI_SHA=1581d4cbdd69a0faf34b2089614fe2a814316a6a
REF_SHA=634b667ee7844f12590117c4c2d7bc0143f2fdd9
BRIDGE_BLOB=64a1cf3ff88a4f655ae7284aa3fb99ed9eab4932
MATHLIB_SHA=d13f23b723b8a846827a245b89c10fc7d3f11612

test "$(git -C "$ROOT/.ci-openai" rev-parse HEAD)" = "$OAI_SHA"
test "$(git -C "$ROOT/.ci-referee" rev-parse HEAD)" = "$REF_SHA"
test "$(git hash-object "$REF/Bridge687.lean")" = "$BRIDGE_BLOB"
test "$(cat "$OPENAI/lean-toolchain")" = 'leanprover/lean4:v4.34.1'
if grep -En '\b(sorry|admit|axiom)\b' "$ATTEMPT/Erdos687Spectral.lean" "$ATTEMPT/ExternalRoot.lean"; then
  echo "HOLE_OR_LOCAL_AXIOM=FAIL"
  exit 1
fi

cd "$OPENAI"
lean --version | tee "$EVIDENCE/lean-version.log"
git rev-parse HEAD > "$EVIDENCE/openai-commit.txt"
lake update 2>&1 | tee "$EVIDENCE/lake-update.log"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$MATHLIB_SHA"
lake exe cache get 2>&1 | tee "$EVIDENCE/mathlib-cache.log"
test -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean || lake -j1 build Mathlib
git -C .lake/packages/mathlib rev-parse HEAD > "$EVIDENCE/mathlib-commit.txt"

lake -j1 build OAI.NumberTheory.Jacobsthal.Main 2>&1 | tee "$EVIDENCE/jacobsthal-build.log"

lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -o "$1/Bridge687.olean" "$1/Bridge687.lean"' _ "$REF" 2>&1 | tee "$EVIDENCE/external-bridge-build.log"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -o "$1/Erdos687Spectral.olean" "$1/Erdos687Spectral.lean"' _ "$ATTEMPT" 2>&1 | tee "$EVIDENCE/core-build.log"
lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; lean -o "$1/ExternalRoot.olean" "$1/ExternalRoot.lean"' _ "$ATTEMPT" "$REF" 2>&1 | tee "$EVIDENCE/root-build.log"
lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; lean --trust=0 "$1/Audit.lean"' _ "$ATTEMPT" "$REF" 2>&1 | tee "$EVIDENCE/axiom-audit.log"

python3 - "$EVIDENCE/axiom-audit.log" <<'PY'
import re,sys
log=open(sys.argv[1],encoding="utf-8").read()
targets=[
"Erdos687Spectral.gramDet_eq_prod",
"Erdos687Spectral.gramDet_pos_iff",
"Erdos687Spectral.gramDet_zero_iff_covered",
"Erdos687Spectral.gramDet_pos_propagates",
"MethlibErdos687.AttemptB.jacobsthal_spectral_bound",
"MethlibErdos687.AttemptB.jacobsthal_no_cover",
"MethlibErdos687.AttemptB.erdos_687_part_ii",
"MethlibErdos687.AttemptB.erdos_687_quantitative"]
allowed={"propext","Classical.choice","Quot.sound"}
for name in targets:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
    if m:
        axioms={a.strip() for a in m.group(1).split(",") if a.strip()}
        if not axioms<=allowed:
            raise SystemExit("THEOREM_AXIOM_AUDIT=FAIL|"+name+"|"+repr(sorted(axioms)))
        print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|"+name+"|"+",".join(sorted(axioms)))
    elif "'"+name+"' does not depend on any axioms" in log:
        print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|"+name+"|none")
    else:
        raise SystemExit("THEOREM_AXIOM_AUDIT=MISSING|"+name)
PY
printf '%s\n' "ERDOS687_ATTEMPT_B=PASS_STANDARD_ONLY" | tee "$EVIDENCE/final-status.txt"
