#!/usr/bin/env python3
"""Check proof-source admission policy and record deterministic source hashes."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


def lean_code(text: str) -> str:
    """Preserve newlines while removing nested comments and string literals."""
    out: list[str] = []
    index = depth = 0
    string = False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif string:
            if char == "\\" and index + 1 < len(text):
                out.extend("  ")
                index += 2
            elif char == '"':
                string = False
                out.append(" ")
                index += 1
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            if end < 0:
                out.extend(" " * (len(text) - index))
                index = len(text)
            else:
                out.extend(" " * (end - index))
                index = end
        elif char == '"':
            string = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1
    if depth or string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(out)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []
    sources: list[dict] = []
    custom_axioms: list[dict] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(root)
        if any(part in {".lake", ".git", "evidence", "__pycache__"} for part in relative.parts):
            continue
        raw = path.read_bytes()
        sources.append({"path": relative.as_posix(), "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)})
        if path.suffix != ".lean":
            continue
        try:
            code = lean_code(raw.decode("utf-8"))
        except (UnicodeError, ValueError) as error:
            errors.append(f"{relative}: {error}")
            continue
        for match in re.finditer(r"\b(sorry|admit|sorryAx)\b", code):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"{relative}:{line}: forbidden proof placeholder {match.group()}")
        for match in re.finditer(r"\baxiom\s+([^\s:(]+)", code):
            name = match.group(1)
            record = {"path": relative.as_posix(), "name": name}
            custom_axioms.append(record)
            if True:
                errors.append(f"unapproved axiom declaration: {record}")
    if len(custom_axioms) > 1:
        errors.append("more than one custom axiom declaration")
    evidence = root / "evidence"
    evidence.mkdir(exist_ok=True)
    (evidence / "sources.json").write_text(json.dumps(sources, indent=2) + "\n", encoding="utf-8")
    (evidence / "sources.sha256").write_text("".join(f"{item['sha256']}  {item['path']}\n" for item in sources), encoding="utf-8")
    print(json.dumps({"status": "PASS" if not errors else "FAIL", "source_count": len(sources), "custom_axioms": custom_axioms, "errors": errors}, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

