"""Validate the endpoint and unified #print axioms reports in a plain Lean compiler log."""

import argparse
import json
import re
from pathlib import Path


NAMESPACE = "Fefferman.ConcreteReal."
THEOREMS = (
    "periodicZeroForceGlobalRegularity_implies_B",
    "PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B",
    "masterABSemantic_iff_A_and_B",
    "masterCDSemantic_iff_C_and_D",
    "abcdPhysicalEndpoints_iff_ABCD",
    "ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD",
    "MASTER_CD_SEMANTIC_IFF_C_AND_D",
    "FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS",
)
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"'\s+(?:does\s+not\s+depend\s+on\s+any\s+axioms|"
    r"depends\s+on\s+axioms:\s*\[(?P<axioms>[^\[\]']*)\])"
    r"[ \t]*$",
    re.MULTILINE,
)


def check(log):
    reports = {}
    errors = []
    for theorem in THEOREMS:
        name = NAMESPACE + theorem
        header = rf"^[ \t]*'{re.escape(name)}(?=['\s]|$)"
        matches = list(re.finditer(header, log, re.MULTILINE))
        if len(matches) != 1:
            errors.append(f"{name}: expected one report, found {len(matches)}")
            continue
        report = REPORT.match(log, matches[0].end())
        if report is None:
            errors.append(f"{name}: malformed axiom report")
            continue
        body = (report.group("axioms") or "").strip()
        axioms = [token.strip() for token in body.split(",")] if body else []
        reports[name] = axioms
        rejected = sorted(set(axioms) - APPROVED)
        if rejected:
            errors.append(f"{name}: unapproved axiom tokens {rejected!r}")
    return reports, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    try:
        reports, errors = check(args.log.read_text(encoding="utf-8"))
    except (OSError, UnicodeError) as exc:
        reports, errors = {}, [str(exc)]
    print(json.dumps({
        "status": "FAIL" if errors else "PASS",
        "approved_axioms": sorted(APPROVED),
        "theorems": reports,
        "errors": errors,
    }, indent=2))
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
