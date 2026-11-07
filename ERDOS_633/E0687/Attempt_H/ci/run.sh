#!/usr/bin/env bash
set -euo pipefail
ATTEMPT="$(cd "$(dirname "$0")/.." && pwd)"
ROOT="$(cd "$ATTEMPT/../../.." && pwd)"
OPENAI="$ROOT/.ci-openai/lean"
EVIDENCE="$ATTEMPT/evidence/finite"
mkdir -p "$EVIDENCE"
test "$(git -C "$ROOT/.ci-openai" rev-parse HEAD)" = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
test "$(cat "$OPENAI/lean-toolchain")" = "leanprover/lean4:v4.34.1"
cd "$OPENAI"
lean --version | tee "$EVIDENCE/lean-version.log"
lake update 2>&1 | tee "$EVIDENCE/lake-update.log"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "d13f23b723b8a846827a245b89c10fc7d3f11612"
lake exe cache get 2>&1 | tee "$EVIDENCE/mathlib-cache.log"
test -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean || lake build Mathlib
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --trust=0 -o "$1/Erdos687AttemptH.olean" "$1/Erdos687AttemptH.lean"' _ "$ATTEMPT" 2>&1 | tee "$EVIDENCE/build.log"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --trust=0 "$1/Audit.lean"' _ "$ATTEMPT" 2>&1 | tee "$EVIDENCE/axiom-audit.log"
python3 "$ATTEMPT/ci/check_axioms.py" finite "$EVIDENCE/axiom-audit.log" | tee "$EVIDENCE/audit-verdict.log"
echo "H_FINITE_CONDITIONAL_ROOT=PASS" | tee "$EVIDENCE/final-status.txt"
