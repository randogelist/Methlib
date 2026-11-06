#!/usr/bin/env python3
"""GitHub Actions audit of the frozen conditional Collatz implication.

--check-source performs read-only Python validation, with no subprocesses.
Full execution is restricted to GITHUB_ACTIONS=true. Theorem dependencies must
already be cached, and the Mathlib umbrella must already be cached or prepared
by the import-only CI bootstrap. This script downloads or builds neither.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone
import uuid


ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB_REVISION = "fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0"
ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SOURCE_HASHES = {
    "FiniteAffine": "21e0b371d9445b9e95eb9621f1917f7e5ec8f63177a4a7b54a0972e79bb7eeb9",
    "RankToCollatz": "8ddcca1ccebeadc1ce6cb10622e09f44962c20b9d93097d0b9fca616a0a30411",
    "BinaryAdapter": "e8724aea01feda038bf65f712d2e33db94916a44c6cfe05710664435f6a72596",
    "Main": "857404e50b3084ef96c556b813b2afc9ce941640b07bb97616487c72d6af97ce",
    "CollatzIntegerBridge": "fb0f96a4ef837245209b5568c11a26767e489c247e42e12a8888650c7a52d95b",
    "major_lean_collatz": "842b01557b267a8edaa1753a46dd463d1a5b8ad726704e90cca038446118ed1d",
}
PROOF_ERROR = re.compile(
    r"\bsorryAx\b|\berror:|declaration uses[^\n]*\bsorry\b", re.IGNORECASE
)
EXACT_CONCLUSION = """import major_lean_collatz

example (n : Nat) :
    PoincareSecond.ordinaryCollatz n =
      (if n % 2 = 0 then n / 2 else 3 * n + 1) := rfl

example {d : Nat} (E : CollatzIntegerBridge.Encoding d)
    (h : CollatzIntegerBridge.integerCheck E = true) :
    forall n : Nat, 0 < n ->
      exists k : Nat,
        PoincareSecond.iterateMap PoincareSecond.ordinaryCollatz k n = 1 := by
  simpa only [PoincareSecond.OrdinaryReachesOne] using
    MajorLeanCollatz.integer_check_implies_collatz E h

example
    (h : exists d : Nat, exists W : PoincareSecond.Certificate d,
      W.check = true) :
    forall n : Nat, 0 < n ->
      exists k : Nat,
        PoincareSecond.iterateMap PoincareSecond.ordinaryCollatz k n = 1 := by
  simpa only [PoincareSecond.OrdinaryReachesOne] using
    PoincareSecond.FINITE_WITNESS_IMPLIES_COLLATZ h
"""


class AuditError(RuntimeError):
    """A failed, absent, or ambiguous verification condition."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8-sig"), object_pairs_hook=unique_object)
    require(isinstance(value, dict), f"Expected a JSON object: {path.name}")
    return value


def powershell_list(source: str, variable: str) -> list[str]:
    matches = re.findall(r"\$" + re.escape(variable) + r"\s*=\s*@\((.*?)\)", source, re.S)
    require(len(matches) == 1, f"Missing or ambiguous original list: {variable}")
    body = matches[0]
    require(not re.sub(r"'[^']*'|[\s,]", "", body), f"Nonliteral original list: {variable}")
    return re.findall(r"'([^']*)'", body)


def check_source(root: Path = ROOT) -> tuple[dict, dict[str, str]]:
    """Validate the frozen source and audit specification; execute nothing."""
    config = read_json(root / "ci/audit-targets.json")
    require(set(config) == {"schema_version", "lean_toolchain", "mathlib_revision",
                           "module_order", "allowed_axioms", "audit_targets"},
            "Unexpected audit configuration fields")
    require(type(config["schema_version"]) is int and config["schema_version"] == 1,
            "Unsupported audit schema")
    require(config["lean_toolchain"] == TOOLCHAIN, "Lean toolchain pin mismatch")
    require(config["mathlib_revision"] == MATHLIB_REVISION, "Mathlib revision pin mismatch")
    require(config["module_order"] == list(SOURCE_HASHES), "Module order mismatch")
    require(config["allowed_axioms"] == list(ALLOWED_AXIOMS), "Axiom allowlist mismatch")
    targets = config["audit_targets"]
    require(isinstance(targets, list) and len(targets) == 13
            and all(isinstance(t, str) and re.fullmatch(r"[A-Za-z_][\w.]*", t) for t in targets)
            and len(set(targets)) == 13, "Expected thirteen distinct named audit targets")
    original = (root / "run.ps1").read_text(encoding="utf-8-sig")
    require(targets == powershell_list(original, "auditTheorems"),
            "Audit targets differ from the original Windows runner")
    require(config["allowed_axioms"] == powershell_list(original, "axiomAllowed"),
            "Axiom allowlist differs from the original Windows runner")
    require(config["module_order"] == powershell_list(original, "needed"),
            "Module order differs from the original Windows runner")
    manifest = read_json(root / "source-manifest.json")
    require(manifest == SOURCE_HASHES, "Frozen source manifest mismatch")
    hashes = {}
    for module, expected in SOURCE_HASHES.items():
        relative = f"src/{module}.lean"
        path = root / relative
        require(path.is_file() and not path.is_symlink(), f"Missing or linked source: {relative}")
        hashes[relative] = sha256(path)
        require(hashes[relative] == expected, f"Source hash mismatch: {module}")
    for relative in ("source-manifest.json", "run.ps1", "ci/audit-targets.json", "ci/run_ci.py"):
        hashes[relative] = sha256(root / relative)
    return config, hashes


def parse_audit_output(theorem: str, output: str) -> list[str]:
    """Require exactly one parseable axiom report for this exact declaration."""
    require(not PROOF_ERROR.search(output), f"Admission or error in audit: {theorem}")
    name = re.escape(theorem)
    none = re.findall(r"'" + name + r"'\s+does not depend on any axioms\b", output)
    reports = re.findall(r"'" + name + r"'\s+depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    require(len(none) + len(reports) == 1, f"Missing or ambiguous axiom report: {theorem}")
    if none:
        return []
    body = reports[0].strip()
    axioms = [part.strip() for part in body.split(",")] if body else []
    require(all(axiom in ALLOWED_AXIOMS for axiom in axioms),
            f"Unapproved or unparseable axioms for {theorem}: {axioms}")
    require(len(axioms) == len(set(axioms)), f"Duplicate axiom entries: {theorem}")
    return axioms


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def git(path: Path, *arguments: str) -> str:
    result = subprocess.run(["git", "-C", str(path), *arguments], capture_output=True,
                            text=True, stdin=subprocess.DEVNULL, timeout=60, check=False)
    require(result.returncode == 0, f"Git provenance failed: {' '.join(arguments)}: {result.stderr.strip()}")
    return result.stdout.strip()


def run_ci(threads: int, timeout: int) -> int:
    require(os.environ.get("GITHUB_ACTIONS") == "true", "Full mode requires GITHUB_ACTIONS=true")
    require(sys.platform == "linux", "Full mode requires a Linux GitHub Actions runner")
    tag = datetime.now(timezone.utc).strftime("ci-%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8]
    evidence = ROOT / "evidence" / tag
    objects, logs = evidence / "olean", evidence / "logs"
    objects.mkdir(parents=True, exist_ok=False)
    logs.mkdir()
    print(f"EVIDENCE={evidence}", flush=True)
    commands = []
    result_lines = []
    env = os.environ.copy()
    status = 1

    def invoke(stage: str, arguments: list[str], cwd: Path, proof: bool = True) -> str:
        print(f"BUILD_START={stage}", flush=True)
        stdout, stderr = logs / f"{stage}.stdout.log", logs / f"{stage}.stderr.log"
        entry = {"stage": stage, "argv": arguments, "cwd": str(cwd)}
        commands.append(entry)
        write_json(evidence / "commands.json", commands)
        with stdout.open("wb") as out, stderr.open("wb") as err:
            try:
                completed = subprocess.run(arguments, cwd=cwd, env=env, stdout=out, stderr=err,
                                           stdin=subprocess.DEVNULL, timeout=timeout, check=False)
            except subprocess.TimeoutExpired as exc:
                entry["timeout_seconds"] = timeout
                write_json(evidence / "commands.json", commands)
                raise AuditError(f"Stage timeout: {stage}") from exc
        entry["exit_code"] = completed.returncode
        write_json(evidence / "commands.json", commands)
        out_text = stdout.read_text(encoding="utf-8", errors="replace")
        err_text = stderr.read_text(encoding="utf-8", errors="replace")
        require(completed.returncode == 0, f"Stage failed: {stage}; exit={completed.returncode}\n{(out_text + err_text)[-6000:]}")
        require(not proof or not PROOF_ERROR.search(out_text + "\n" + err_text),
                f"Stage reported an admission or error: {stage}")
        print(f"BUILD_PASS={stage}", flush=True)
        return out_text

    try:
        config, before = check_source()
        write_json(evidence / "source-and-config-hashes.json", before)
        for relative in ("source-manifest.json", "ci/audit-targets.json"):
            (evidence / Path(relative).name).write_bytes((ROOT / relative).read_bytes())
        print("SOURCE_HASHES=PASS", flush=True)
        lean_value = os.environ.get("LEAN_EXE", "")
        cache_value = os.environ.get("MATHLIB_CACHE_ROOT", "")
        require(bool(lean_value) and Path(lean_value).is_absolute(), "Set LEAN_EXE to the native compiler's absolute path")
        require(bool(cache_value) and Path(cache_value).is_absolute(), "Set MATHLIB_CACHE_ROOT to the pinned Mathlib checkout")
        lean, cache = Path(lean_value).resolve(), Path(cache_value).resolve()
        require(lean.is_file() and os.access(lean, os.X_OK), "LEAN_EXE is not executable")
        require(not (lean.parent.name == "bin" and lean.parent.parent.name == ".elan"), "LEAN_EXE must identify the native compiler, not the elan shim")
        require(cache.is_dir(), "Mathlib checkout is missing")
        require(Path(git(cache, "rev-parse", "--show-toplevel")).resolve() == cache,
                "MATHLIB_CACHE_ROOT must be the Mathlib Git checkout root")
        revision = git(cache, "rev-parse", "HEAD")
        require(revision == MATHLIB_REVISION, "Mathlib checkout revision mismatch")
        require(not git(cache, "status", "--porcelain", "--untracked-files=no"),
                "Mathlib checkout has modified tracked files")
        require((cache / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
                "Mathlib lean-toolchain mismatch")
        library = cache / ".lake/build/lib/lean"
        require((library / "Mathlib.olean").is_file(), "Mathlib.olean is missing after cache/bootstrap preparation")
        origin_file = ROOT / "evidence/bootstrap/mathlib-umbrella-origin.txt"
        umbrella_origin = origin_file.read_text(encoding="utf-8").strip()
        require(umbrella_origin in ("OFFICIAL_CACHE", "CI_IMPORT_ONLY_UMBRELLA_FROM_CACHED_DEPENDENCIES"),
                "Unrecognized Mathlib umbrella origin")
        libraries = [library]
        packages = cache / ".lake/packages"
        if packages.is_dir():
            libraries.extend(path / ".lake/build/lib/lean" for path in sorted(packages.iterdir())
                             if (path / ".lake/build/lib/lean").is_dir())
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [objects, *libraries])
        env["LEAN_NUM_THREADS"] = str(threads)
        (evidence / "lean-path.txt").write_text(env["LEAN_PATH"] + "\n", encoding="utf-8")
        version = invoke("LeanVersion", [str(lean), "--version"], ROOT, proof=False).strip()
        require(re.match(r"^Lean \(version 4\.34\.0-rc1,", version) is not None,
                f"Unexpected compiler version: {version}")
        (evidence / "lean-version.txt").write_text(version + "\n", encoding="utf-8")
        provenance = {
            "repository_commit": git(ROOT, "rev-parse", "HEAD"),
            "repository_tracked_changes": git(ROOT, "status", "--porcelain", "--untracked-files=no"),
            "github": {key: os.environ.get(key, "") for key in (
                "GITHUB_REPOSITORY", "GITHUB_SHA", "GITHUB_REF", "GITHUB_RUN_ID",
                "GITHUB_RUN_ATTEMPT", "GITHUB_WORKFLOW", "RUNNER_OS", "RUNNER_ARCH")},
            "lean_executable": str(lean), "lean_executable_sha256": sha256(lean),
            "lean_version": version, "lean_toolchain": TOOLCHAIN,
            "mathlib_checkout": str(cache), "mathlib_revision": revision,
            "mathlib_toolchain_sha256": sha256(cache / "lean-toolchain"),
            "mathlib_lake_manifest_sha256": sha256(cache / "lake-manifest.json"),
            "mathlib_umbrella_source_sha256": sha256(cache / "Mathlib.lean"),
            "mathlib_umbrella_olean_sha256": sha256(library / "Mathlib.olean"),
            "mathlib_umbrella_origin": umbrella_origin,
            "mathlib_umbrella_origin_record_sha256": sha256(origin_file),
            "cached_library_paths": [str(p) for p in libraries],
            "cache_provenance": "PINNED_CHECKOUT_AND_RECORDED_CACHE_HASHES_NOT_INDEPENDENTLY_REBUILT",
            "cache_hash_coverage": "Mathlib.olean umbrella only; not every dependency object",
            "local_source_modules": "COMPILED_FRESH", "theorem_dependencies": "EXISTING_CACHE_ONLY",
            "source_and_config_hashes": before,
        }
        write_json(evidence / "provenance.json", provenance)
        (evidence / "mathlib-lake-manifest.json").write_bytes((cache / "lake-manifest.json").read_bytes())
        for module in config["module_order"]:
            output = objects / f"{module}.olean"
            require(not output.exists(), f"Object unexpectedly pre-exists: {module}")
            invoke(module, [str(lean), f"-j{threads}", "-o", str(output),
                            str(ROOT / "src" / f"{module}.lean")], ROOT / "src")
            require(output.is_file(), f"Missing freshly compiled object: {module}")
        require(check_source()[1] == before, "Source/configuration changed during compilation")
        exact = evidence / "ExactConclusion.lean"
        exact.write_text(EXACT_CONCLUSION, encoding="utf-8")
        invoke("ExactConclusion", [str(lean), f"-j{threads}", str(exact)], evidence)
        audits = {}
        for theorem in config["audit_targets"]:
            stage = "Audit_" + theorem.replace(".", "_")
            source = evidence / f"{stage}.lean"
            source.write_text(f"import major_lean_collatz\n#check {theorem}\n#print axioms {theorem}\n", encoding="utf-8")
            output = invoke(stage, [str(lean), f"-j{threads}", str(source)], evidence)
            audits[theorem] = parse_audit_output(theorem, output)
            print(f"AXIOM_AUDIT_STANDARD_ONLY={theorem}", flush=True)
        write_json(evidence / "named-axiom-audits.json", audits)
        require(check_source()[1] == before, "Source/configuration changed during audits")
        result_lines = [
            "BUILD_AND_NAMED_AXIOM_AUDITS=PASS", "EXACT_CONCLUSION_TYPECHECK=PASS",
            "RESULT_SCOPE=CONDITIONAL_INTEGER_ROOT_AND_NECESSARY_FILTERS",
            "C_SOURCE_EQUIVALENCE=NOT_ESTABLISHED", "COLLATZ_WITNESS=NOT_SUPPLIED",
            "C_SEARCH=NOT_INCLUDED",
            "MATHLIB_CACHE_PROVENANCE=PINNED_CHECKOUT_NOT_INDEPENDENTLY_REBUILT",
            "RESULT=PASS",
        ]
        status = 0
    except Exception as exc:
        result_lines = ["RESULT=FAIL", f"REASON={type(exc).__name__}: {exc}",
                        "RESULT_SCOPE=CONDITIONAL_IMPLICATION_NOT_VERIFIED_BY_THIS_RUN",
                        "C_SOURCE_EQUIVALENCE=NOT_ESTABLISHED", "COLLATZ_WITNESS=NOT_SUPPLIED",
                        "C_SEARCH=NOT_INCLUDED"]
    finally:
        write_json(evidence / "object-hashes.json", {str(p.relative_to(objects)): sha256(p)
                   for p in sorted(objects.rglob("*")) if p.is_file()})
        write_json(evidence / "log-hashes.json", {p.name: sha256(p) for p in sorted(logs.iterdir()) if p.is_file()})
        (evidence / "result.txt").write_text("\n".join(result_lines) + "\n", encoding="utf-8")
        print("\n".join(result_lines), flush=True)
        summary = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary:
            with Path(summary).open("a", encoding="utf-8") as stream:
                stream.write("## Conditional finite-witness implication\n\n")
                stream.write(f"Result: **{'PASS' if status == 0 else 'FAIL'}**.\n\n")
                stream.write("Scope: the existing checker-to-ordinary-Collatz implication and necessary filters. "
                             "No accepted witness, C implementation equivalence, or C search is supplied.\n\n")
                stream.write(f"Lean: `{TOOLCHAIN}`; Mathlib: `{MATHLIB_REVISION}`.\n\n")
                stream.write("Cached theorem dependencies were reused; their objects were not independently rebuilt. "
                             "The Mathlib umbrella origin is recorded separately in provenance.json.\n\n")
                stream.write(f"Evidence: `{evidence.relative_to(ROOT)}`.\n\n")
        print(f"EVIDENCE={evidence}", flush=True)
    return status


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-source", action="store_true", help="Validate source/configuration only; invoke no compiler")
    parser.add_argument("--threads", type=int, default=min(16, os.cpu_count() or 1))
    parser.add_argument("--stage-timeout", type=int, default=3600, help="Maximum seconds per external stage")
    args = parser.parse_args(argv)
    try:
        require(1 <= args.threads <= 64, "--threads must be between 1 and 64")
        require(args.stage_timeout > 0, "--stage-timeout must be positive")
        if args.check_source:
            check_source()
            print("SOURCE_HASHES=PASS\nAUDIT_CONFIG=PASS\nCHECK_SOURCE=PASS\nLEAN_INVOCATIONS=0")
            return 0
        return run_ci(args.threads, args.stage_timeout)
    except Exception as exc:
        print(f"RESULT=FAIL\nREASON={type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
