#!/usr/bin/env python3
"""Hash extension inputs and reject placeholders/custom axioms."""
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



def check(root: Path) -> dict:
    records, errors = [], []
    files = sorted((root / "SingularityDisprovement").rglob("*.lean"))
    aggregate = root / "SingularityDisprovement.lean"
    if aggregate.exists():
        files.append(aggregate)
    files += sorted((root / "ci_singularity").rglob("*"))
    for path in files:
        if not path.is_file() or "__pycache__" in path.parts:
            continue
        raw = path.read_bytes()
        relative = path.relative_to(root).as_posix()
        records.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest(),
                        "bytes": len(raw)})
        if path.suffix != ".lean":
            continue
        try:
            code = lean_code(raw.decode("utf-8"))
        except (UnicodeError, ValueError) as error:
            errors.append(relative + ": " + str(error))
            continue
        for match in re.finditer(r"\b(sorry|admit|sorryAx|axiom)\b", code):
            errors.append(relative + ":" + str(code.count("\n", 0, match.start()) + 1)
                          + ": forbidden declaration/placeholder " + match.group())
    return {"status": "PASS" if not errors else "FAIL",
            "sources": records, "errors": errors}


if __name__ == "__main__":
    answer = check(Path.cwd())
    print(json.dumps(answer, indent=2))
    raise SystemExit(0 if answer["status"] == "PASS" else 1)

