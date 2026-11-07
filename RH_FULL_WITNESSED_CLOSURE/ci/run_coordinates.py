#!/usr/bin/env python3
"""Cached native replay of finite coordinate tests. This is not RH admission."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import uuid
from datetime import datetime, timezone

ROOT = pathlib.Path(__file__).resolve().parents[1]
NS = "RHFullWitnessedClosure.CoordinateTesting."
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_NAMES = [
    "coordinateCheck_iff", "coordinateCheck_sound", "admitted_coordinate",
    "accepted_singleCell", "exampleFinitePass_accepted",
    "exampleBadDenominator_rejected", "exampleCoverageGap_rejected",
    "exampleMissingCoverage_rejected", "exampleCutoffMismatch_rejected",
    "exampleBadInequality_rejected", "exampleMissingSignAlternative_rejected",
]


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest() -> None:
    root = ROOT.resolve()
    manifest = root / "provenance/source-manifest.sha256"
    for line in manifest.read_text(encoding="utf-8").splitlines():
        expected, rel = line.split("  ", 1)
        path = (root / rel).resolve()
        if not path.is_relative_to(root) or digest(path) != expected:
            raise ValueError("SOURCE_MANIFEST_MISMATCH=" + rel)


def audit_axioms(text: str, names: list[str]) -> None:
    if "sorryAx" in text:
        raise ValueError("SORRY_AX_FOUND")
    for short in names:
        name = NS + short
        starts = re.findall(rf"^'{re.escape(name)}'[^\n]*", text, re.MULTILINE)
        reports = re.findall(
            rf"^'{re.escape(name)}' (does not depend on any axioms|"
            rf"depends on axioms:\s*\[[^\]]*\])[ \t]*$", text, re.MULTILINE
        )
        if len(starts) != 1 or len(reports) != 1:
            raise ValueError("MISSING_OR_AMBIGUOUS_AXIOM_AUDIT=" + name)
        report = reports[0]
        if report == "does not depend on any axioms":
            print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|" + name)
            continue
        entries = report[report.index("[") + 1:report.rindex("]")]
        axioms = {x.strip() for x in entries.split(",") if x.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise ValueError("UNAPPROVED_AXIOMS=" + name + ":" + str(sorted(axioms)))
        print("THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY|" + name)


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=pathlib.Path,
                        default=ROOT / "coordinates/example.json")
    parser.add_argument("--lean", type=pathlib.Path)
    parser.add_argument("--check-source", action="store_true")
    args = parser.parse_args()
    verify_manifest()
    print("SOURCE_MANIFEST=PASS")
    if args.check_source:
        return 0
    if os.name != "nt":
        raise ValueError("NATIVE_WINDOWS_REQUIRED")
    candidate = args.input.resolve()
    if not candidate.is_file():
        raise ValueError("COORDINATE_INPUT_NOT_FOUND=" + str(candidate))
    profile = pathlib.Path(os.environ.get("USERPROFILE", str(pathlib.Path.home())))
    lean = args.lean or pathlib.Path(os.environ.get(
        "LEAN_EXE", str(profile / ".elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe")
    ))
    lean = lean.resolve()
    if not lean.is_file():
        raise ValueError("PINNED_LEAN_433_NOT_FOUND=" + str(lean))
    std = lean.parent.parent / "lib/lean/Std.olean"
    init = lean.parent.parent / "lib/lean/Init.olean"
    if not std.is_file() or not init.is_file():
        raise ValueError("PINNED_STD_CACHE_NOT_FOUND")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
    evidence = ROOT / "evidence/coordinates" / stamp
    build = ROOT / "_build/coordinates"
    evidence.mkdir(parents=True)
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.pop("LEAN_SYSROOT", None)
    env["LEAN_PATH"] = str(build)
    env["LEAN_NUM_THREADS"] = "4"
    provenance = {
        "status": "STARTED", "scope": "FINITE_COORDINATE_SPECIFICATION_ONLY",
        "source_manifest_sha256": digest(ROOT / "provenance/source-manifest.sha256"),
        "input_sha256": digest(candidate), "lean_exe_sha256": digest(lean),
        "std_olean_sha256": digest(std), "init_olean_sha256": digest(init),
    }
    summary = evidence / "result.json"
    summary.write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")

    def run(arguments: list[str], name: str, *, expected: int | None = 0) -> subprocess.CompletedProcess[str]:
        proc = subprocess.run(arguments, cwd=ROOT, env=env, text=True,
                              encoding="utf-8", errors="replace",
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (evidence / name).write_text(proc.stdout, encoding="utf-8")
        print(proc.stdout, end="")
        if expected is not None and proc.returncode != expected:
            raise ValueError("COMMAND_FAILED=" + name + "|EXIT=" + str(proc.returncode))
        return proc

    try:
        version = run([str(lean), "--version"], "lean-version.log").stdout
        if not re.search(r"Lean \(version 4\.33\.0(?:,|\))", version):
            raise ValueError("LEAN_VERSION_MISMATCH")
        print("MODE=NATIVE_WINDOWS_CACHED_STD")
        print("NETWORK=NOT_USED")
        print("LAKE=NOT_USED")
        print("EVIDENCE=" + str(evidence))
        fingerprint = {key: provenance[key] for key in (
            "lean_exe_sha256", "std_olean_sha256", "init_olean_sha256"
        )}
        for module, imports in (("CoordinateData", []), ("CoordinateTesting", ["CoordinateData"])):
            source = ROOT / (module + ".lean")
            obj = build / (module + ".olean")
            metadata = build / (module + ".cache.json")
            key = {**fingerprint, "source_sha256": digest(source),
                   "imports": {m: digest(build / (m + ".olean")) for m in imports}}
            old = json.loads(metadata.read_text()) if metadata.exists() else {}
            if obj.exists() and old.get("key") == key and old.get("olean_sha256") == digest(obj):
                print("CACHED_MODULE_REUSE=" + module)
            else:
                metadata.unlink(missing_ok=True)
                obj.unlink(missing_ok=True)
                run([str(lean), "-o", str(obj), str(source)], module + ".log")
                if not obj.is_file():
                    raise ValueError("OLEAN_MISSING=" + module)
                metadata.write_text(json.dumps({"key": key, "olean_sha256": digest(obj)}, indent=2) + "\n")
                print("COMPILE=PASS|" + module)
        audit = run([str(lean), "CoordinateAudit.lean"], "coordinate-audit.log")
        audit_axioms(audit.stdout, AUDIT_NAMES)
        negative = run([str(lean), "negative/CoordinateNegativeAdmission.lean"],
                       "negative-admission.log", expected=None)
        if negative.returncode == 0:
            raise ValueError("NEGATIVE_CONTROL_INCORRECTLY_ADMITTED")
        if "proved that the proposition" not in negative.stdout or "is false" not in negative.stdout:
            raise ValueError("NEGATIVE_CONTROL_UNEXPECTED_FAILURE")
        if any(s in negative.stdout for s in ("unknown identifier", "unexpected token", "unknown module")):
            raise ValueError("NEGATIVE_CONTROL_UNEXPECTED_FAILURE")
        print("NEGATIVE_CONTROL=PASS")
        generated = evidence / "SubmittedCoordinates.lean"
        run([sys.executable, "ci/coordinate_input.py", "--input", str(candidate),
             "--output", str(generated)], "coordinate-generation.log")
        generated_meta = json.loads(generated.with_name(generated.name + ".metadata.json").read_text(encoding="utf-8"))
        if generated_meta["input_sha256"] != provenance["input_sha256"]:
            raise ValueError("COORDINATE_INPUT_CHANGED_DURING_RUN")
        if generated_meta["lean_source_sha256"] != digest(generated):
            raise ValueError("GENERATED_COORDINATE_HASH_MISMATCH")
        provenance["generated_source_sha256"] = generated_meta["lean_source_sha256"]
        provenance["canonical_json_sha256"] = generated_meta["canonical_json_sha256"]
        accepted = run([str(lean), str(generated)], "coordinate-admission.log", expected=None)
        if accepted.returncode != 0:
            provenance["status"] = "FINITE_COORDINATE_NOT_ADMITTED"
            print("FINITE_COORDINATE_ADMISSION=NOT_ESTABLISHED")
            print("RH_ADMISSION=BLOCKED")
            return 2
        audit_axioms(accepted.stdout, ["submittedCoordinate_valid"])
        provenance["status"] = "FINITE_COORDINATE_ADMISSION_PASS"
        provenance["rh_admission"] = "BLOCKED_ANALYTIC_OBLIGATIONS"
        print("FINITE_COORDINATE_ADMISSION=PASS")
        print("EXACT_CONCLUSION=CoordinateWellFormed submittedCoordinate")
        print("ACTUAL_XI_BOUND_VERIFICATION=OPEN")
        print("RH_ADMISSION=BLOCKED_ANALYTIC_OBLIGATIONS")
        print("RH_PROMOTION=NONE")
        print("RUN=PASS_FINITE_COORDINATE_TEST_ONLY")
        return 0
    except Exception as exc:
        provenance["status"] = "FAILED"
        provenance["reason"] = str(exc)
        raise
    finally:
        summary.write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as exc:
        print("RUN=FAIL", file=sys.stderr)
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
