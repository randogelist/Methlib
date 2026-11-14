#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import re

HEX = re.compile(r"^[0-9a-fA-F]*$")


def load_hex(path: pathlib.Path) -> bytes:
    chunks: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0]
        chunks.append("".join(line.split()))
    text = "".join(chunks)
    if not text:
        raise SystemExit("candidate packet is empty")
    if len(text) % 2:
        raise SystemExit("candidate hex has odd length")
    if not HEX.fullmatch(text):
        raise SystemExit("candidate contains non-hexadecimal data")
    return bytes.fromhex(text)


def render(data: bytes) -> str:
    entries = ", ".join(str(b) for b in data)
    return f"""import Architecture

namespace RHFullWitnessedClosure

def committedWitness : ByteArray :=
  ByteArray.mk #[{entries}]

#eval committedWitness.size

end RHFullWitnessedClosure
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("target", type=pathlib.Path)
    args = parser.parse_args()
    data = load_hex(args.source)
    if len(data) > 64 * 1024 * 1024:
        raise SystemExit("candidate exceeds 64 MiB")
    args.target.write_text(render(data), encoding="utf-8")
    print(f"WITNESS_BYTES={len(data)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
