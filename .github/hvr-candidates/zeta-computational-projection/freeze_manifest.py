#!/usr/bin/env python3
"""Freeze an ordered plan and its local source files; does not invoke Lean."""
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent
plan_path = root / "plan.json"
plan = json.loads(plan_path.read_text(encoding="utf-8"))
if not isinstance(plan, list) or not plan:
    raise SystemExit("plan must be a nonempty array")
mods = [e.get("module") for e in plan if isinstance(e, dict)]
if len(mods) != len(plan) or len(set(mods)) != len(mods) or any(
    not isinstance(x, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", x) for x in mods
):
    raise SystemExit("invalid or duplicate modules")
sources = [root / "sources" / (mod + ".lean") for mod in mods]
actual = set((root / "sources").glob("*.lean"))
if set(sources) != actual or any(not p.is_file() for p in sources):
    raise SystemExit("source files do not exactly match plan")
paths = [plan_path, *sources]
manifest = "".join(
    hashlib.sha256(p.read_bytes()).hexdigest() + "  " + p.relative_to(root).as_posix() + "\n"
    for p in paths
)
(root / "sources.sha256").write_text(manifest, encoding="utf-8", newline="\n")
print("MANIFEST_WRITTEN modules=" + str(len(mods)))

