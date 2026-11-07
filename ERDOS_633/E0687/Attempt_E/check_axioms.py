#!/usr/bin/env python3
"""Check the actual theorem-level Lean #print axioms output."""
from pathlib import Path
import re
import sys
log=Path(sys.argv[1]).read_text(errors="replace")
mode=sys.argv[2]
req=["Erdos687AttemptE.momentCertificate_eq_coveredCount",
     "Erdos687AttemptE.quadratic_finite_certificate",
     "Erdos687AttemptE.quadratic_all_moduli",
     "Erdos687AttemptE.quadratic_prime_cutoff"]
if mode=="external":
    req += ["Erdos687AttemptE.imported_jacobsthal_quadratic",
            "Erdos687AttemptE.imported_prime_cutoff_quadratic"]
allowed={"propext","Classical.choice","Quot.sound"}
if "sorryAx" in log or "declaration uses sorry" in log:
    sys.exit("AUDIT=FAIL_SORRYAX")
found=set()
for line in log.splitlines():
    for name in req:
        if name not in line or ("depends on axioms:" not in line and "does not depend on any axioms" not in line):
            continue
        m=re.search(r"depends on axioms:\s*\[(.*?)\]",line)
        if "depends on axioms:" in line and m is None:
            sys.exit("AUDIT=FAIL_MALFORMED: "+line)
        axioms={x.strip() for x in (m.group(1).split(",") if m else []) if x.strip()}
        if axioms - allowed:
            sys.exit("AUDIT=FAIL_NONSTANDARD: "+name+" "+str(sorted(axioms-allowed)))
        found.add(name)
        print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|"+name)
if set(req)-found:
    sys.exit("AUDIT=FAIL_MISSING: "+str(sorted(set(req)-found)))
print("AUDIT=PASS_STANDARD_ONLY")
