#!/usr/bin/env python3
"""Strict theorem-level Lean axiom audit for ERDOS_633/E0687/Attempt_G."""
import pathlib
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOTS = {
    "finite": [
        "Erdos687AttemptG.gram_psd_iff_survivors_positive",
        "Erdos687AttemptG.jacobsthal_quadratic_to_prime_gram",
    ],
    "external": [
        "Erdos687AttemptG.external_jacobsthal_quadratic",
        "Erdos687AttemptG.erdos_687_prime_hankel_external_root",
    ],
}

def main() -> int:
    if len(sys.argv) != 3 or sys.argv[1] not in ROOTS:
        print("USAGE=python3 check_axioms.py finite|external audit.log")
        return 2
    mode, path = sys.argv[1:]
    content = pathlib.Path(path).read_text(encoding="utf-8", errors="replace")
    if re.search(r"\bsorryAx\b|\bsorry\b", content):
        print("THEOREM_AXIOM_AUDIT=FAIL_SORRY")
        return 3
    for root in ROOTS[mode]:
        m = re.search(
            r"['\x22]?" + re.escape(root)
            + r"['\x22]?\s+depends on axioms:\s*\[([^\]]*)\]",
            content, re.S,
        )
        if m:
            found = set(x.strip() for x in m.group(1).split(",") if x.strip())
            unknown = found - ALLOWED
            if unknown:
                print("THEOREM_AXIOM_AUDIT=FAIL_UNAPPROVED_AXIOM|"
                      + root + "|" + ",".join(sorted(unknown)))
                return 4
            print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|"
                  + root + "|" + ",".join(sorted(found)))
        elif re.search(r"['\x22]?" + re.escape(root)
                      + r"['\x22]?\s+does not depend on any axioms", content):
            print("THEOREM_AXIOM_AUDIT=PASS_NO_AXIOMS|" + root)
        else:
            print("THEOREM_AXIOM_AUDIT=INCONCLUSIVE_MISSING_ROOT|" + root)
            return 5
    print("AUDIT_ROOT_COUNT=" + str(len(ROOTS[mode])))
    return 0

if __name__ == "__main__":
    sys.exit(main())
