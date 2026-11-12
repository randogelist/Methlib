#!/usr/bin/env python3
"""Fail-closed audit of one fresh Lean transcript and an explicit declaration list."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

AXIOM_PRINT = re.compile(
    r"(?:'(?P<quoted>[^'\n]+)'|(?P<bare>[A-Za-z_][A-Za-z0-9_.]*))\s+"
    r"(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"does not depend on any axioms)",
    re.MULTILINE,
)


def audit(text: str, spec: dict) -> dict:
    errors: list[str] = []
    if spec.get("schema_version") != 1:
        errors.append("unsupported audit schema")
    standard = set(spec.get("standard_axioms", []))
    if standard != {"propext", "Classical.choice", "Quot.sound"}:
        errors.append("standard axiom set differs from the frozen policy")
    declarations = spec.get("declarations", [])
    if not declarations:
        errors.append("empty audit declaration list")
    expected: dict[str, dict] = {}
    for item in declarations:
        name = item.get("name")
        if not isinstance(name, str) or not name:
            errors.append("invalid declaration name")
            continue
        if name in expected:
            errors.append(f"duplicate expected declaration: {name}")
        expected[name] = item
    if "sorryAx" in text:
        errors.append("sorryAx occurs in audit transcript")
    if re.search(r"(^|\n).*\berror:", text):
        errors.append("Lean error occurs in audit transcript")

    observed: dict[str, list[str]] = {}
    for match in AXIOM_PRINT.finditer(text):
        name = match.group("quoted") or match.group("bare")
        axioms = sorted({a.strip() for a in (match.group("axioms") or "").split(",") if a.strip()})
        if name in observed:
            errors.append(f"duplicate axiom report: {name}")
        observed[name] = axioms
    for name in sorted(set(expected) - set(observed)):
        errors.append(f"missing axiom report: {name}")
    for name in sorted(set(observed) - set(expected)):
        errors.append(f"unexpected axiom report: {name}")
    records = []
    for name, item in expected.items():
        allowed = standard | set(item.get("additional_allowed_axioms", []))
        required = set(item.get("required_axioms", []))
        extra = allowed - standard
        if not extra <= {"SingularClosure.AX6"}:
            errors.append(f"unapproved custom axiom policy: {name}")
        if not required <= allowed:
            errors.append(f"required axiom outside allowed set: {name}")
        marker = item.get("exact_type_marker")
        if not isinstance(marker, str) or not marker.startswith("EXACT_TYPE_PASS:"):
            errors.append(f"missing exact-type marker specification: {name}")
        elif text.splitlines().count(marker) != 1:
            errors.append(f"exact-type marker must occur exactly once: {name}")
        if name in observed:
            actual = set(observed[name])
            if actual - allowed:
                errors.append(f"unapproved axioms for {name}: {sorted(actual - allowed)}")
            if required - actual:
                errors.append(f"required axioms absent for {name}: {sorted(required - actual)}")
            records.append({"name": name, "axioms": sorted(actual)})
    return {
        "schema_version": 1,
        "status": "PASS" if not errors else "FAIL",
        "declaration_count": len(expected),
        "declarations": records,
        "errors": errors,
        "endpoint_completion_inferred": False,
        "scope": "Only the explicit compiled declarations and exact-type checks in this audit.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("transcript", type=Path)
    parser.add_argument("spec", type=Path)
    args = parser.parse_args()
    try:
        result = audit(args.transcript.read_text(encoding="utf-8"), json.loads(args.spec.read_text(encoding="utf-8")))
    except (OSError, ValueError, TypeError, KeyError) as error:
        result = {"status": "FAIL", "errors": [str(error)], "endpoint_completion_inferred": False}
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
