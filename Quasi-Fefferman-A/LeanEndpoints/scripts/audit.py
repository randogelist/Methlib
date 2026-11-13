"""Pinned QFA source inspection and external Windows cached Lean audit."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text: str) -> str:
    """Remove nested block comments, line comments, and string literals."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            out.append('""')
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("UNTERMINATED_LEAN_COMMENT")
    return "".join(out)


def inspect_sources(base: Path) -> dict:
    manifest = json.loads((base / "endpoint-manifest.json").read_text(encoding="utf-8"))
    if set(manifest["allowed_axioms"]) != ALLOWED_AXIOMS:
        raise ValueError("AXIOM_POLICY_MISMATCH")
    if manifest["mathlib"] != MATHLIB_REV or manifest["lean"] != "4.33.0":
        raise ValueError("BASELINE_MISMATCH")
    for path, expected in manifest["sources"].items():
        if digest(base / path) != expected:
            raise ValueError(f"SOURCE_DIGEST_MISMATCH:{path}")
    lean_paths = {p.relative_to(base).as_posix() for p in base.rglob("*.lean")
                  if not ({".lake", "evidence"} & set(p.relative_to(base).parts))}
    expected_lean = {p for p in manifest["sources"] if p.endswith(".lean")}
    if lean_paths != expected_lean:
        raise ValueError("LEAN_SOURCE_INVENTORY_MISMATCH")
    for path in sorted(lean_paths):
        code = lean_code((base / path).read_text(encoding="utf-8"))
        if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", code):
            raise ValueError(f"UNAPPROVED_PROOF_CONSTRUCTION:{path}")
    names = [entry["name"] for entry in manifest["declarations"]]
    if not names or len(names) != len(set(names)):
        raise ValueError("EMPTY_OR_DUPLICATE_DECLARATION_LIST")
    lock = json.loads((base / "lake-manifest.json").read_text(encoding="utf-8"))
    locked = {p["name"]: p["rev"] for p in lock["packages"]}
    if locked != manifest["dependency_revisions"]:
        raise ValueError("DEPENDENCY_LOCK_MISMATCH")
    if locked.get("mathlib") != MATHLIB_REV:
        raise ValueError("MATHLIB_LOCK_MISMATCH")
    if (base / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.0":
        raise ValueError("TOOLCHAIN_FILE_MISMATCH")
    return manifest


def inspect_axioms(text: str, names: list[str]) -> dict:
    if re.search(r"\bsorryAx\b|\buses ['`]sorry['`]|\berror(?:\([^\n)]*\))?:", text):
        raise ValueError("LEAN_ERROR_OR_SORRY_DEPENDENCY")
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports += [(name, "") for name in
                re.findall(r"'([^']+)' does not depend on any axioms", text)]
    if sorted(name for name, _ in reports) != sorted(names):
        raise ValueError("EXACT_DECLARATION_AUDIT_MISMATCH")
    result = {}
    for name, raw in reports:
        raw = re.sub(r"\.\{[^{}]*\}", "", raw)
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(f"UNAPPROVED_AXIOMS:{name}:{sorted(axioms - ALLOWED_AXIOMS)}")
        begin, end = f"TYPE_BEGIN:{name}\n", f"TYPE_END:{name}\n"
        if text.count(begin) != 1 or text.count(end) != 1:
            raise ValueError(f"TYPE_MARKER_MISMATCH:{name}")
        begin_at, end_at = text.index(begin), text.index(end)
        if begin_at >= end_at:
            raise ValueError(f"REVERSED_TYPE_MARKERS:{name}")
        statement = text[begin_at + len(begin):end_at].strip()
        if not statement:
            raise ValueError(f"EMPTY_COMPILER_TYPE:{name}")
        result[name] = {"type": statement, "axioms": sorted(axioms)}
    return result


def parser_self_test() -> None:
    """Pure text fixtures; this function never starts Lean or Lake."""
    name = "Fixture.exact_endpoint"
    good = (f"TYPE_BEGIN:{name}\n{name} : True\nTYPE_END:{name}\n"
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
    assert set(inspect_axioms(good, [name])[name]["axioms"]) == ALLOWED_AXIOMS
    reversed_markers = (f"TYPE_END:{name}\nTYPE_BEGIN:{name}\n{name} : True\n"
                        f"'{name}' depends on axioms: [propext]\n")
    for invalid in [good + good, reversed_markers, good.replace("Quot.sound", "sorryAx"),
                    good.replace("Quot.sound", "Custom.assumption"),
                    good.replace("TYPE_END", "MISSING_END"),
                    good + "error(lean.unknownIdentifier): failed\n"]:
        try:
            inspect_axioms(invalid, [name])
        except ValueError:
            continue
        raise ValueError("AUDIT_PARSER_ACCEPTED_INVALID_FIXTURE")


def command(base: Path, args: list[str], log: Path) -> str:
    result = subprocess.run(args, cwd=base, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                            errors="replace", check=False)
    log.write_text(result.stdout, encoding="utf-8")
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise RuntimeError(f"COMMAND_FAILED:{args!r}:EXIT={result.returncode}")
    return result.stdout


def external_audit(base: Path, manifest: dict) -> None:
    if os.name != "nt":
        raise RuntimeError("EXTERNAL_NATIVE_WINDOWS_ONLY")
    evidence = base / "evidence"
    evidence.mkdir(exist_ok=True)
    manifest_bytes = (base / "endpoint-manifest.json").read_bytes()
    if json.loads(manifest_bytes) != manifest:
        raise ValueError("MANIFEST_CHANGED_BEFORE_EXTERNAL_RUN")
    initial_manifest_sha = hashlib.sha256(manifest_bytes).hexdigest()
    status = {"root_status": "B_TIER_ROOT_FORMALIZATION_PENDING",
              "endpoint_status": "PENDING", "cache_policy": "MATHLIB_CACHE_AND_INCREMENTAL_LAKE",
              "source_manifest_sha256": initial_manifest_sha}

    def unchanged_source_snapshot() -> None:
        if digest(base / "endpoint-manifest.json") != initial_manifest_sha:
            raise ValueError("MANIFEST_CHANGED_DURING_EXTERNAL_RUN")
        inspect_sources(base)

    def dependency_snapshot(phase: str) -> None:
        for package, rev in manifest["dependency_revisions"].items():
            path = base / ".lake" / "packages" / package
            actual = command(base, ["git", "-C", str(path), "rev-parse", "HEAD"],
                             evidence / f"{phase}-revision-{package}.txt").strip()
            if actual != rev:
                raise ValueError(f"DEPENDENCY_REVISION_MISMATCH:{package}")
            dirty = command(base, ["git", "-C", str(path), "status", "--porcelain",
                                   "--untracked-files=all"],
                            evidence / f"{phase}-status-{package}.txt")
            if dirty.strip():
                raise ValueError(f"MODIFIED_DEPENDENCY_SOURCE:{package}")

    try:
        version = command(base, ["lake", "env", "lean", "--version"], evidence / "lean-version.txt")
        if not re.search(r"version 4\.33\.0,", version):
            raise ValueError("EXTERNAL_COMPILER_VERSION_MISMATCH")
        status["compiler"] = version.strip()
        # Native dependency objects are downloaded; existing objects remain cached.
        command(base, ["lake", "exe", "cache", "get"], evidence / "mathlib-cache.log")
        dependency_snapshot("before")
        unchanged_source_snapshot()
        command(base, ["lake", "build", "QFA"], evidence / "build.log")
        unchanged_source_snapshot()
        log = command(base, ["lake", "env", "lean", "Audit.lean"], evidence / "axioms.log")
        names = [entry["name"] for entry in manifest["declarations"]]
        status["declarations"] = inspect_axioms(log, names)
        unchanged_source_snapshot()
        dependency_snapshot("after")
        status["endpoint_status"] = "EXTERNAL_COMPILER_AND_EXACT_AXIOM_AUDIT_PASS"
        status["physical_QFA_root_inferred"] = False
        print("EXTERNAL_SCALAR_ENDPOINT_AUDIT_PASS; QFA_ROOT_FORMALIZATION_PENDING")
    except Exception as error:
        status["endpoint_status"] = "FAIL"
        status["error"] = str(error)
        raise
    finally:
        (evidence / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        (evidence / "source-manifest.json").write_bytes(manifest_bytes)


def main() -> int:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--static", action="store_true")
    modes.add_argument("--external", action="store_true")
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1]
    parser_self_test()
    manifest = inspect_sources(base)
    if args.static:
        print(json.dumps({"source_inspection": "PASS", "audit_parser_fixtures": "PASS",
                          "declarations": len(manifest["declarations"]),
                          "local_lean_executions": 0, "external_verification": "PENDING"}))
    else:
        external_audit(base, manifest)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(f"QFA_AUDIT_FAILURE:{exc}", file=sys.stderr)
        sys.exit(1)
