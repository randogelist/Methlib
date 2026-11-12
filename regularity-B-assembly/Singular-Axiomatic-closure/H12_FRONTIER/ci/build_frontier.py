#!/usr/bin/env python3
"""External cached build and fail-closed exact-declaration audit. No proof promotion by source alone."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "evidence" / "frontier"
OUT.mkdir(parents=True, exist_ok=True)

def run(args: list[str], path: Path) -> int:
    with path.open("w", encoding="utf-8") as out:
        p = subprocess.Popen(args, cwd=ROOT, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
        assert p.stdout is not None
        for line in p.stdout:
            print(line, end="", flush=True)
            out.write(line)
        return p.wait()

def main() -> int:
    plan = json.loads((ROOT / "ci/frontier_plan.json").read_text(encoding="utf-8"))
    sources = sorted((ROOT / "SingularClosure/H12Frontier").rglob("*.lean"))
    for source in sources:
        text = source.read_text(encoding="utf-8")
        if re.search(r"\b(sorry|admit|axiom|unsafe)\b", text):
            raise RuntimeError(f"forbidden proof source token: {source}")
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in ROOT.rglob("*.lean") if ".lake" not in p.parts and "evidence" not in p.parts}
    (OUT / "source-sha256.json").write_text(json.dumps(hashes, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    records = []
    failed = False
    for entry in plan["entries"]:
        ident = entry["id"]
        rec = dict(entry, source_commit=os.environ.get("GITHUB_SHA"),
                   status="BUILD_FAILED", exact_type="NOT_RUN", axiom_audit="NOT_RUN")
        build_rc = run(["lake", "build", entry["module"]], OUT / f"{ident}-build.log")
        if build_rc == 0:
            audit_rc = run(["lake", "env", "lean", entry["audit"]], OUT / f"{ident}-axioms.log")
            if audit_rc == 0:
                check_rc = run([sys.executable, "ci/check_axioms.py",
                                str(OUT / f"{ident}-axioms.log"), entry["spec"]], OUT / f"{ident}-audit.json")
                if check_rc == 0:
                    rec.update(status="COMPILE_AND_AUDIT_PASS", exact_type="PASS", axiom_audit="PASS_STANDARD_ONLY")
                else:
                    rec["status"] = "AUDIT_FAILED"
            else:
                rec["status"] = "EXACT_TYPE_OR_COMPILER_FAILED"
        failed |= rec["status"] != "COMPILE_AND_AUDIT_PASS"
        records.append(rec)
        print("FRONTIER_RESULT:" + json.dumps(rec, sort_keys=True), flush=True)
        (OUT / "results.json").write_text(json.dumps({"entries": records,
            "completion_requires_scope_review": True}, indent=2)+"\n", encoding="utf-8")
    return int(failed)

if __name__ == "__main__":
    sys.exit(main())
