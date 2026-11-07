import re
import sys
from pathlib import Path

log = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
names = [
    "spike_certificate_iff",
    "external_partial_plus_certificate",
    "certificate_excludes_covers",
    "small_rational_certificate_iff",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
failed = False
for name in names:
    qualified = "Erdos687AttemptC." + name
    pat = r"['`]?" + re.escape(qualified) + r"['`]? depends on axioms: \\[([^\\]]*)\\]"
    match = re.search(pat, log)
    if match is None:
        print(f"THEOREM_AXIOM_AUDIT=FAIL_MISSING|{qualified}")
        failed = True
        continue
    axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
    extra = axioms - allowed
    verdict = "PASS_STANDARD_ONLY" if not extra else "FAIL_UNAPPROVED"
    print(f"THEOREM_AXIOM_AUDIT={verdict}|{qualified}|{','.join(sorted(axioms))}")
    failed |= bool(extra)
if "sorryAx" in log or "admit" in log:
    print("AUDIT=FAIL_SORRY_OR_ADMIT")
    failed = True
print("ROOT=A_TIER_CANDIDATE; FRONTIER_BOUND=OPEN")
sys.exit(1 if failed else 0)
