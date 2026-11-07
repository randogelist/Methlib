#!/usr/bin/env python3
import pathlib, re, sys
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOTS = {
  "finite": [
    "Erdos687AttemptH.prefix_second_difference",
    "Erdos687AttemptH.gapCheck_iff_siftedY",
    "Erdos687AttemptH.threshold_iff_gap",
    "Erdos687AttemptH.sampleCheck_iff_gapCheck",
    "Erdos687AttemptH.SiftedPeriod.interior_not_coprime",
    "Erdos687AttemptH.curvatureCheck_iff_certifiedPeriod",
    "Erdos687AttemptH.erdosPrimeCheck_iff_certifiedPeriod",
  ],
  "external": [
    "Erdos687AttemptH.erdos_687_part_ii",
    "Erdos687AttemptH.erdos_687_quantitative",
    "Erdos687.erdos_687.parts.ii",
    "Erdos687.Y_isBigO",
  ],
}
kind, filename = sys.argv[1:]
s = pathlib.Path(filename).read_text(encoding="utf-8", errors="replace")
if re.search(r"\bsorryAx\b", s):
    sys.exit("THEOREM_AXIOM_AUDIT=FAIL_SORRYAX")
for root in ROOTS[kind]:
    m = re.search(r"['\x22]?" + re.escape(root) + r"['\x22]?\s+depends on axioms:\s*\[([^\]]*)\]", s, re.S)
    if m:
        axioms = {x.strip() for x in m.group(1).split(",") if x.strip()}
        if not axioms <= ALLOWED:
            sys.exit(f"THEOREM_AXIOM_AUDIT=FAIL|{root}|{sorted(axioms - ALLOWED)}")
    elif not re.search(r"['\x22]?" + re.escape(root) + r"['\x22]?\s+does not depend on any axioms", s):
        sys.exit("THEOREM_AXIOM_AUDIT=MISSING|" + root)
    print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|" + root)
print("AUDITED_ROOTS=" + str(len(ROOTS[kind])))
