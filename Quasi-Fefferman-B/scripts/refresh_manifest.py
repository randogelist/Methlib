"""Snapshot explicit candidate declarations; Python only, never invokes Lean."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
modules = []
for source in sorted((root / "QuasiFeffermanB").glob("*.lean")):
    text = source.read_text(encoding="utf-8")
    names = re.findall(r"^theorem\s+([A-Za-z_][A-Za-z_0-9'.]*)", text, re.M)
    if not names:
        continue  # definitions-only imports are hashed separately below
    modules.append({
        "module": f"QuasiFeffermanB.{source.stem}",
        "source": source.relative_to(root).as_posix(),
        "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "declarations": [name.removeprefix("_root_.") if name.startswith("_root_.")
                         else f"QuasiFeffermanB.{name}" for name in names],
        "scope": "exact source declaration; broader Q/A contracts remain pending",
    })
sources = {
    source.relative_to(root).as_posix(): hashlib.sha256(source.read_bytes()).hexdigest()
    for source in sorted((root / "QuasiFeffermanB").glob("*.lean"))
}
manifest = {
    "schema": 1,
    "foundation_sha": "09dfe94a1ef150e21d09df3013fbe09002ef139c",
    "lean": "4.33.0",
    "mathlib": "db584cd6d46c92f209a44c0f1c829460d327499d",
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "root_status": "A_TIER_CANDIDATE; no root promotion",
    "contract_status": {**{f"Q{i:02}": "PENDING" for i in range(15)},
                        **{f"A{i:02}": "PENDING" for i in range(1, 12)}},
    "sources": sources,
    "modules": modules,
}
(root / "endpoint-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"modules": len(modules), "sources": len(sources),
                  "declarations": sum(len(m["declarations"]) for m in modules)}))
