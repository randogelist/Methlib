#!/usr/bin/env python3
"""Fail-closed theorem-level axiom audit for Erdős 687 Attempt_D."""
import argparse
import json
import pathlib
import re
import sys

CORE = [
    "prime_partition",
    "finite_margin_excludes_cover",
    "finite_budget_excludes_cover",
    "strong_of_exact_margin",
    "strong_of_short_budget",
]
EXTERNAL = [
    "no_shift_cover_of_jacobsthal",
    "external_quadratic",
    "external_iterated_log",
    "external_plus_exact_margin",
    "external_improved_plus_short_budget",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True)
    parser.add_argument("--scope", required=True, choices=["core", "external"])
    args = parser.parse_args()
    log = pathlib.Path(args.log).read_text(encoding="utf-8", errors="replace")
    endpoints = CORE if args.scope == "core" else EXTERNAL
    status = {"scope": args.scope, "status": "PASS_STANDARD_ONLY", "theorems": {}}
    for short in endpoints:
        name = "Erdos687AttemptD." + short
        pat = r"'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
        found = re.search(pat, log)
        if not found:
            status["status"] = "FAIL_MISSING_AXIOM_REPORT"
            status["theorems"][name] = "MISSING"
            continue
        axioms = sorted(x.strip() for x in (found.group(1) or "").split(",") if x.strip())
        status["theorems"][name] = axioms
        if any(x not in ALLOWED for x in axioms):
            status["status"] = "FAIL_UNAPPROVED_AXIOM"
    if re.search(r"sorryAx|admitAx", log):
        status["status"] = "FAIL_FORBIDDEN_AXIOM"
    path = pathlib.Path(args.log).with_name(args.scope + "-audit.json")
    path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print("AXIOM_AUDIT=" + status["status"])
    print("REPORT=" + str(path))
    for theorem, axioms in status["theorems"].items():
        print("THEOREM_AXIOM_AUDIT=" + theorem + ":" + str(axioms))
    return 0 if status["status"] == "PASS_STANDARD_ONLY" else 1

if __name__ == "__main__":
    sys.exit(main())
