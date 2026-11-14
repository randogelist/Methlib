#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys
from typing import Iterable

ROOT = pathlib.Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"(^|\W)(sorry|admit|axiom|native_decide)(\W|$)|sorryAx",
    re.IGNORECASE | re.MULTILINE,
)


def run(cmd: list[str], *, log: str, expect: int | None = 0) -> subprocess.CompletedProcess[str]:
    EVIDENCE.mkdir(exist_ok=True)
    path = EVIDENCE / log
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    path.write_text(proc.stdout, encoding="utf-8")
    print(proc.stdout, end="")
    if expect is not None and proc.returncode != expect:
        raise SystemExit(f"command failed ({proc.returncode}): {' '.join(cmd)}")
    return proc


def env_file(path: pathlib.Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, value = line.split("=", 1)
        result[key] = value
    return result


def scan_forbidden(paths: Iterable[pathlib.Path]) -> None:
    bad: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        if FORBIDDEN.search(text):
            bad.append(str(path.relative_to(ROOT)))
    if bad:
        raise SystemExit("forbidden proof token in: " + ", ".join(bad))


def audit_axioms(log: pathlib.Path, declarations: list[str]) -> None:
    text = log.read_text(encoding="utf-8")
    if "sorryAx" in text:
        raise SystemExit("sorryAx found in theorem audit")
    for decl in declarations:
        no_axioms = f"'{decl}' does not depend on any axioms"
        if no_axioms in text:
            continue
        pattern = re.compile(
            rf"'{re.escape(decl)}' depends on axioms:\s*\[([^\]]*)\]",
            re.MULTILINE,
        )
        match = pattern.search(text)
        if not match:
            raise SystemExit(f"missing axiom report for {decl}")
        found = {x.strip() for x in match.group(1).split(",") if x.strip()}
        extra = found - ALLOWED_AXIOMS
        if extra:
            raise SystemExit(f"unapproved axioms for {decl}: {sorted(extra)}")


def verify_manifest() -> None:
    manifest = ROOT / "provenance" / "source-manifest.sha256"
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        digest, rel = raw.split("  ", 1)
        data = (ROOT / rel).read_bytes()
        got = hashlib.sha256(data).hexdigest()
        if got != digest:
            raise SystemExit(f"source manifest mismatch: {rel}")


def compile_base() -> None:
    run(["lake", "build", "RHFullWitnessedClosure"], log="build.log")
    run(["lake", "env", "lean", "Architecture.lean"], log="architecture.log")
    run(["lake", "env", "lean", "NegativeControl.lean"], log="negative-control.log")
    negative = run(
        ["lake", "env", "lean", "negative/NegativeAdmission.lean"],
        log="negative-admission.log",
        expect=None,
    )
    if negative.returncode == 0:
        raise SystemExit("negative control was incorrectly admitted")
    if "proved that the proposition" not in negative.stdout or "is false" not in negative.stdout:
        raise SystemExit("negative control failed for an unexpected reason")
    if "unexpected token" in negative.stdout or "unknown identifier" in negative.stdout:
        raise SystemExit("negative control contains parser/name failure")
    print("NEGATIVE_CONTROL=PASS")


def candidate_mode(status: dict[str, str]) -> None:
    concrete = ROOT / "ConcreteSystem.lean"
    root_file = ROOT / "RH_FULL_WITNESSED_CLOSURE.lean"
    if not concrete.is_file() or not root_file.is_file():
        raise SystemExit("candidate mode requires ConcreteSystem.lean and RH_FULL_WITNESSED_CLOSURE.lean")

    expected_sha = (ROOT / "witness" / "candidate.sha256").read_text(encoding="utf-8").strip()
    packet = ROOT / "witness" / "candidate.hex"
    hex_chunks: list[str] = []
    for raw_line in packet.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0]
        hex_chunks.append("".join(line.split()))
    hex_text = "".join(hex_chunks)
    if not hex_text:
        raise SystemExit("candidate packet is empty")
    raw = bytes.fromhex(hex_text)
    got_sha = hashlib.sha256(raw).hexdigest()
    if expected_sha != got_sha:
        raise SystemExit("witness SHA-256 mismatch")

    run(
        [sys.executable, "ci/generate_witness.py", "witness/candidate.hex", "GeneratedWitness.lean"],
        log="generate-witness.log",
    )
    scan_forbidden([
        ROOT / "ConcreteSystem.lean",
        ROOT / "RH_FULL_WITNESSED_CLOSURE.lean",
        ROOT / "GeneratedWitness.lean",
    ])
    run(["lake", "env", "lean", "ConcreteSystem.lean"], log="concrete-system.log")
    run(["lake", "env", "lean", "GeneratedWitness.lean"], log="generated-witness.log")
    run(["lake", "env", "lean", "RH_FULL_WITNESSED_CLOSURE.lean"], log="root.log")

    root_log = EVIDENCE / "root.log"
    root_text = root_log.read_text(encoding="utf-8")
    exact = "RHFullWitnessedClosure.RH_FULL_WITNESSED_CLOSURE : RiemannHypothesis"
    if exact not in root_text:
        raise SystemExit("exact native RH root type not printed")
    audit_axioms(root_log, [
        "RHFullWitnessedClosure.committedWitnessAccepted",
        "RHFullWitnessedClosure.RH_FULL_WITNESSED_CLOSURE",
    ])
    print("WITNESS_ADMISSION=PASS")
    print("ROOT_NATIVE_RH=PASS")
    print("CI_CANDIDATE=PASS")
    print("PROMOTION=!!!_PENDING_INDEPENDENT_REVIEW")


def empty_mode() -> None:
    if (ROOT / "ConcreteSystem.lean").exists() or (ROOT / "RH_FULL_WITNESSED_CLOSURE.lean").exists():
        raise SystemExit("EMPTY state forbids concrete root files")
    text = (ROOT / "witness" / "candidate.hex").read_text(encoding="utf-8")
    if "EMPTY" not in text:
        raise SystemExit("EMPTY state requires placeholder witness")
    if (ROOT / "witness" / "candidate.sha256").read_text(encoding="utf-8").strip() != "UNSET":
        raise SystemExit("EMPTY state requires UNSET witness hash")
    print("ADMISSION_READY=YES")
    print("WITNESS_PRESENT=NO")
    print("PROMOTION=BLOCKED_AT_!!!")
    print("CI_SCAFFOLD=PASS")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-source", action="store_true")
    args = parser.parse_args()

    verify_manifest()
    if args.check_source:
        print("SOURCE_MANIFEST=PASS")
        return 0

    status = env_file(ROOT / "STATUS.env")
    state = status.get("RH_WITNESS_STATE")
    if status.get("PROMOTION_CAP") != "!!!":
        raise SystemExit("promotion cap must remain !!! in repository scaffold")

    scan_forbidden([ROOT / "Architecture.lean", ROOT / "NegativeControl.lean"])
    compile_base()

    if state == "EMPTY":
        empty_mode()
    elif state == "CANDIDATE":
        candidate_mode(status)
    else:
        raise SystemExit(f"unsupported RH_WITNESS_STATE={state!r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
