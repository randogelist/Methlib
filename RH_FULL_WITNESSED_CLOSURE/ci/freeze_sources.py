#!/usr/bin/env python3
"""Maintainer operation: freeze repository-tracked package bytes; never runs Lean."""
from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    # The explicit git inventory excludes runtime files and candidate inputs.
    listed = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "."],
        cwd=ROOT,
    ).decode("utf-8").split("\0")
    manifest = "provenance/source-manifest.sha256"
    lines = []
    for rel in sorted(set(listed) - {"", manifest}):
        path = ROOT / rel
        if not path.is_file():
            raise SystemExit("MISSING_SOURCE=" + rel)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(digest + "  " + rel)
    (ROOT / manifest).write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("FROZEN_SOURCE_FILES=" + str(len(lines)))


if __name__ == "__main__":
    main()
