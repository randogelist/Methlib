#!/usr/bin/env python3
"""Fail-closed audit of one fresh Lean transcript and an explicit declaration list."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

AXIOM_PRINT = re.compile(
    r"^[ \t]*(?:'(?P<quoted>[^'\r\n]+)'|(?P<bare>[A-Za-z_][A-Za-z0-9_.]*))[ \t]+"
    r"(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"does not depend on any axioms)[ \t]*\r?$",
    re.MULTILINE,
)
REPORT_START = re.compile(
    r"^[ \t]*(?:'[^'\r\n]+'|[A-Za-z_][A-Za-z0-9_.]*)[ \t]+"
    r"(?:depends on axioms:|does not depend on any axioms)", re.MULTILINE,
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def string_list(value: object) -> bool:
    return isinstance(value, list) and all(isinstance(x, str) and bool(x) for x in value)


def marker_line(line: str) -> str:
    """Lean #eval String prints quotes; IO.println prints a bare line."""
    line = line.strip()
    if line.startswith('"') and line.endswith('"'):
        try:
            decoded = json.loads(line)
            if isinstance(decoded, str):
                return decoded
        except ValueError:
            pass
    return line


def audit(text: str, spec: dict) -> dict:
    errors: list[str] = []
    if not isinstance(spec, dict):
        spec = {}
        errors.append("audit specification is not an object")
    if type(spec.get("schema_version")) is not int or spec.get("schema_version") != 1:
        errors.append("unsupported audit schema")
    standard_spec = spec.get("standard_axioms")
    if (not string_list(standard_spec) or len(standard_spec) != 3
            or set(standard_spec) != STANDARD_AXIOMS):
        errors.append("standard axiom set differs from the frozen policy")
    declarations = spec.get("declarations")
    if not isinstance(declarations, list):
        declarations = []
        errors.append("declarations must be an array")
    if not declarations:
        errors.append("empty audit declaration list")
    expected: dict[str, dict] = {}
    for item in declarations:
        if not isinstance(item, dict):
            errors.append("declaration entry is not an object")
            continue
        name = item.get("name")
        if not isinstance(name, str) or not name:
            errors.append("invalid declaration name")
            continue
        if name in expected:
            errors.append(f"duplicate expected declaration: {name}")
        expected[name] = item
    if "sorryAx" in text:
        errors.append("sorryAx occurs in audit transcript")
    if "declaration uses 'sorry'" in text:
        errors.append("unproved declaration warning occurs in audit transcript")
    if re.search(r"(^|\n).*\berror:", text):
        errors.append("Lean error occurs in audit transcript")

    observed: dict[str, list[str]] = {}
    matches = list(AXIOM_PRINT.finditer(text))
    if {match.start() for match in matches} != {match.start() for match in REPORT_START.finditer(text)}:
        errors.append("malformed axiom report")
    for match in matches:
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
    marker_lines = [marker_line(line) for line in text.splitlines()]
    for name, item in expected.items():
        additions = item.get("additional_allowed_axioms")
        required_spec = item.get("required_axioms")
        if not isinstance(additions, list) or additions:
            errors.append(f"additional axiom allowances must be an empty array: {name}")
        if not string_list(required_spec):
            errors.append(f"required axioms must be an array of names: {name}")
            required_spec = []
        required = set(required_spec)
        if not required <= STANDARD_AXIOMS:
            errors.append(f"required axiom outside allowed set: {name}")
        marker = item.get("exact_type_marker")
        if marker != f"EXACT_TYPE_PASS:{name}":
            errors.append(f"exact-type marker does not identify its declaration: {name}")
        elif marker_lines.count(marker) != 1:
            errors.append(f"exact-type marker must occur exactly once: {name}")
        if name in observed:
            actual = set(observed[name])
            if actual - STANDARD_AXIOMS:
                errors.append(f"unapproved axioms for {name}: {sorted(actual - STANDARD_AXIOMS)}")
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

