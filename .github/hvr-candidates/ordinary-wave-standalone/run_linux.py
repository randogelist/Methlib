#!/usr/bin/env python3
"""Cached Lean 4.34.0-rc1 ordered build, with exact named axiom audits.

This is an external-runner script. Authoring/check-plan does not invoke Lean.
"""
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+\Z")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_plan():
    plan = json.loads((ROOT / "plan.json").read_text(encoding="utf-8"))
    if not isinstance(plan, list) or not plan:
        raise ValueError("plan must be a nonempty array")
    modules, theorem_names = set(), set()
    for entry in plan:
        if not isinstance(entry, dict) or set(entry) != {"module", "theorems"}:
            raise ValueError("each entry requires only module and theorems")
        mod, names = entry["module"], entry["theorems"]
        if not isinstance(mod, str) or not IDENT.fullmatch(mod) or mod in modules:
            raise ValueError("invalid or duplicate module: " + str(mod))
        modules.add(mod)
        if not isinstance(names, list):
            raise ValueError("theorems must be an array")
        for name in names:
            if not isinstance(name, str) or not NAME.fullmatch(name) or name in theorem_names:
                raise ValueError("invalid or duplicate theorem: " + str(name))
            theorem_names.add(name)
    if not theorem_names:
        raise ValueError("at least one named theorem is required")
    expected = {"plan.json"} | {"sources/" + mod + ".lean" for mod in modules}
    actual_files = {p.relative_to(ROOT).as_posix() for p in (ROOT / "sources").glob("*.lean")}
    if actual_files != expected - {"plan.json"}:
        raise ValueError("source files do not exactly match plan")
    supplied = {}
    for line in (ROOT / "sources.sha256").read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (plan\.json|sources/[A-Za-z_][A-Za-z0-9_]*\.lean)", line)
        if not match or match.group(2) in supplied:
            raise ValueError("malformed or duplicate manifest entry")
        supplied[match.group(2)] = match.group(1)
    if set(supplied) != expected:
        raise ValueError("manifest does not exactly match the plan and sources")
    for name, expected_hash in supplied.items():
        if digest(ROOT / name) != expected_hash:
            raise ValueError("source hash mismatch: " + name)
    return plan


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-plan", action="store_true")
    args = parser.parse_args()
    plan = read_plan()
    print("SOURCE_HASHES=PASS MODULES=" + str(len(plan)), flush=True)
    if args.check_plan:
        print("LEAN_EXECUTION=NOT_REQUESTED", flush=True)
        return 0
    lean = Path(os.environ["LEAN_EXE"]).resolve(strict=True)
    cache = Path(os.environ["MATHLIB_CACHE_ROOT"]).resolve(strict=True)
    lib = cache / ".lake/build/lib/lean"
    witness = lib / "Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.olean"
    if not witness.is_file():
        raise ValueError("cached Mathlib witness not found")
    ver = subprocess.run([str(lean), "--version"], capture_output=True, text=True, check=True).stdout.strip()
    if not ver.startswith("Lean (version 4.34.0-rc1,") or "linux" not in ver.lower():
        raise ValueError("expected native Linux Lean 4.34.0-rc1: " + ver)
    tag = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%d-%H%M%S-%f")
    ev = ROOT / "evidence-linux" / tag
    objdir = ev / "olean"
    objdir.mkdir(parents=True)
    depdirs = sorted(p for p in (cache / ".lake/packages").glob("*/.lake/build/lib/lean") if p.is_dir())
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [objdir, lib, *depdirs]))
    data = {
        "lean_version": ver,
        "compiler_sha256": digest(lean),
        "manifest_sha256": digest(ROOT / "sources.sha256"),
        "mathlib_witness_sha256": digest(witness),
        "mathlib_full_object_provenance": "NOT_INDEPENDENTLY_VERIFIED",
        "dependency_trace": "NOT_REQUESTED",
        "dependency_coverage": "UNVERIFIED",
        "modules": {},
    }
    (ev / "lean-path.txt").write_text(env["LEAN_PATH"] + "\n", encoding="utf-8")
    (ev / "lean-version.txt").write_text(ver + "\n", encoding="utf-8")
    print("EVIDENCE=" + str(ev), flush=True)
    print("LEAN_EXE=" + str(lean), flush=True)
    print(ver, flush=True)

    def run(stage, arguments):
        print("STAGE_START=" + stage, flush=True)
        with (ev / (stage + ".stdout.log")).open("wb") as out, (ev / (stage + ".stderr.log")).open("wb") as err:
            result = subprocess.run([str(lean), *map(str, arguments)], cwd=ROOT / "sources", env=env, stdout=out, stderr=err)
        if result.returncode:
            print("STAGE_FAIL=" + stage, flush=True)
            for suffix in (".stdout.log", ".stderr.log"):
                print((ev / (stage + suffix)).read_text(encoding="utf-8", errors="replace"), flush=True)
            return False
        print("STAGE_PASS=" + stage, flush=True)
        return True

    ok = True
    for entry in plan:
        mod = entry["module"]
        record = data["modules"][mod] = {"source_sha256": digest(ROOT / "sources" / (mod + ".lean"))}
        obj = objdir / (mod + ".olean")
        if not run("build_" + mod, ["-o", obj, mod + ".lean"]) or not obj.is_file():
            record["build"] = "FAIL"
            ok = False
            break
        record["build"] = "PASS"
        record["object_sha256"] = digest(obj)
        if not entry["theorems"]:
            continue
        audit = ev / ("Audit_" + mod + ".lean")
        audit.write_text("import " + mod + "\n" + "".join("#check " + n + "\n#print axioms " + n + "\n" for n in entry["theorems"]), encoding="utf-8")
        record["audit_source_sha256"] = digest(audit)
        if not run("audit_" + mod, [audit]):
            record["audit"] = "FAIL"
            ok = False
            break
        log = (ev / ("audit_" + mod + ".stdout.log")).read_text(encoding="utf-8", errors="replace")
        for name in entry["theorems"]:
            pattern = (r"'" + re.escape(name) + r"' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]|(?P<none>does not depend on any axioms))")
            match = re.search(pattern, log, re.DOTALL)
            if not match:
                print("MISSING_AXIOM_REPORT=" + name, flush=True)
                ok = False
                continue
            axioms = set() if match.group("none") is not None else {x.strip() for x in match.group("axioms").split(",") if x.strip()}
            bad = axioms - ALLOWED
            if bad:
                print("UNAPPROVED_AXIOM=" + name + " AXIOMS=" + ",".join(sorted(bad)), flush=True)
                ok = False
            else:
                print("AXIOM_AUDIT_STANDARD_ONLY=" + name, flush=True)
        record["audit"] = "STANDARD_ONLY" if ok else "FAIL"
        if not ok:
            break
    (ev / "provenance.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    result = "PASS" if ok else "FAIL"
    summary = "RESULT=" + result + "\nSCOPE=NAMED_THEOREMS_ONLY\nDEPENDENCY_TRACE=NOT_REQUESTED\nDEPENDENCY_COVERAGE=UNVERIFIED\nMATHLIB_FULL_CACHE_PROVENANCE=NOT_INDEPENDENTLY_VERIFIED\n"
    (ev / "result.txt").write_text(summary, encoding="utf-8")
    print(summary, end="", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("RUNNER_ERROR=" + str(exc), file=sys.stderr, flush=True)
        raise SystemExit(2)

