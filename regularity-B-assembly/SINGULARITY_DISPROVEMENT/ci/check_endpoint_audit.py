#!/usr/bin/env python3
"""Fail-closed standard-axiom and exact-signature transcript verification."""
from __future__ import annotations

import json
import re
from pathlib import Path
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_PRINT = re.compile(
    r"(?:'(?P<quoted>[^'\n]+)'|(?P<bare>[A-Za-z_][A-Za-z0-9_.]*))\s+"
    r"(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"does not depend on any axioms)", re.MULTILINE)


def audit(text: str, name: str) -> dict:
    errors = []
    marker = "EXACT_TYPE_PASS:" + name
    if text.splitlines().count(marker) != 1:
        errors.append("exact signature marker absent or duplicated")
    if "sorryAx" in text or re.search(r"\bdeclaration uses 'sorry'", text):
        errors.append("proof placeholder in transcript")
    if re.search(r"(^|\n).*\berror:", text):
        errors.append("compiler error in transcript")
    reports = list(AXIOM_PRINT.finditer(text))
    if len(reports) != 1:
        errors.append("expected exactly one theorem-level axiom report")
    axioms = []
    for report in reports:
        observed = report.group("quoted") or report.group("bare")
        if observed != name:
            errors.append("axiom report refers to a different theorem")
        axioms = sorted({x.strip() for x in (report.group("axioms") or "").split(",")
                         if x.strip()})
        if set(axioms) - STANDARD:
            errors.append("unapproved axioms: " + repr(sorted(set(axioms) - STANDARD)))
    return {"status": "PASS" if not errors else "FAIL", "name": name,
            "axioms": axioms, "exact_type_marker": marker, "errors": errors}


if __name__ == "__main__":
    result = audit(Path(sys.argv[1]).read_text(encoding="utf-8"), sys.argv[2])
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["status"] == "PASS" else 1)
