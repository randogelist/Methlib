"Pinned QFA conditional physical-root audit on native Windows Lean."

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"
BASELINE_COMPILED_COMMIT = "9b6ca616b2f26e0222decb872401752e8320babe"
BASELINE_RUN_ID = "43532773061"
BASELINE_ROOTS = 108
ROOT_NAMES = [
    "QFA.PhysicalRoot.selectedTail_restricted_singleton",
    "QFA.PhysicalRoot.selectedTail_smooth",
    "QFA.PhysicalRoot.selectedTail_root_conclusion",
    "QFA.PhysicalRoot.QUASI_FEFFERMAN_A",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text: str) -> str:
    out: list[str] = []
    depth = 0
    i = 0
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


def audit_names(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    begins = re.findall(r'TYPE_BEGIN:([^"]+)', text)
    ends = re.findall(r'TYPE_END:([^"]+)', text)
    checks = re.findall(r"#check\s+@([A-Za-z0-9_'.]+)", text)
    prints = re.findall(r"#print\s+axioms\s+([A-Za-z0-9_'.]+)", text)
    if not begins or begins != ends or begins != checks or begins != prints:
        raise ValueError(f"AUDIT_REGISTRY_MISMATCH:{path.name}")
    if len(begins) != len(set(begins)):
        raise ValueError(f"DUPLICATE_AUDIT_NAME:{path.name}")
    return begins


def inspect_axioms(text: str, names: list[str]) -> dict[str, dict]:
    if re.search(r"\bsorryAx\b|\buses ['`]sorry['`]|\berror(?:\([^\n)]*\))?:", text):
        raise ValueError("LEAN_ERROR_OR_SORRY_DEPENDENCY")
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports += [(name, "") for name in
                re.findall(r"'([^']+)' does not depend on any axioms", text)]
    if sorted(name for name, _ in reports) != sorted(names):
        raise ValueError("EXACT_DECLARATION_AUDIT_MISMATCH")
    result: dict[str, dict] = {}
    for name, raw in reports:
        raw = re.sub(r"\.\{[^{}]*\}", "", raw)
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(
                f"UNAPPROVED_AXIOMS:{name}:{sorted(axioms - ALLOWED_AXIOMS)}"
            )
        begin = f"TYPE_BEGIN:{name}\n"
        end = f"TYPE_END:{name}\n"
        if text.count(begin) != 1 or text.count(end) != 1:
            raise ValueError(f"TYPE_MARKER_MISMATCH:{name}")
        begin_at = text.index(begin)
        end_at = text.index(end)
        if begin_at >= end_at:
            raise ValueError(f"REVERSED_TYPE_MARKERS:{name}")
        statement = text[begin_at + len(begin):end_at].strip()
        if not statement:
            raise ValueError(f"EMPTY_COMPILER_TYPE:{name}")
        result[name] = {"type": statement, "axioms": sorted(axioms)}
    return result


def inspect_sources(base: Path) -> tuple[dict, dict, list[str], list[str]]:
    root_manifest = json.loads(
        (base / "root-manifest.json").read_text(encoding="utf-8")
    )
    if set(root_manifest["allowed_axioms"]) != ALLOWED_AXIOMS:
        raise ValueError("ROOT_AXIOM_POLICY_MISMATCH")
    if root_manifest["lean"] != "4.33.0" or root_manifest["mathlib"] != MATHLIB_REV:
        raise ValueError("ROOT_BASELINE_MISMATCH")

    for relative, expected in root_manifest["root_sources"].items():
        if digest(base / relative) != expected:
            raise ValueError(f"ROOT_SOURCE_DIGEST_MISMATCH:{relative}")

    baseline_manifest_path = base / "endpoint-manifest.json"
    if digest(baseline_manifest_path) != root_manifest["baseline"]["endpoint_manifest_sha256"]:
        raise ValueError("BASELINE_ENDPOINT_MANIFEST_MISMATCH")
    baseline = json.loads(baseline_manifest_path.read_text(encoding="utf-8"))
    if baseline["lean"] != "4.33.0" or baseline["mathlib"] != MATHLIB_REV:
        raise ValueError("BASELINE_ENDPOINT_VERSION_MISMATCH")
    if set(baseline["allowed_axioms"]) != ALLOWED_AXIOMS:
        raise ValueError("BASELINE_ENDPOINT_AXIOM_POLICY_MISMATCH")

    for relative, expected in baseline["sources"].items():
        if digest(base / relative) != expected:
            raise ValueError(f"BASELINE_SOURCE_DIGEST_MISMATCH:{relative}")

    verification = base.parent / "CI" / BASELINE_COMPILED_COMMIT / "VERIFICATION.txt"
    if digest(verification) != root_manifest["baseline"]["verification_sha256"]:
        raise ValueError("BASELINE_VERIFICATION_DIGEST_MISMATCH")
    verification_text = verification.read_text(encoding="utf-8")
    for required in [
        f"compiled_commit: {BASELINE_COMPILED_COMMIT}",
        f"github_run: {BASELINE_RUN_ID}",
        "run_conclusion: completed / success",
        "endpoint_evidence: PASS; LE001-LE108",
    ]:
        if required not in verification_text:
            raise ValueError(f"BASELINE_VERIFICATION_CONTENT_MISMATCH:{required}")

    baseline_names = audit_names(base / "Audit.lean")
    root_names = audit_names(base / "RootAudit.lean")
    if len(baseline_names) != BASELINE_ROOTS:
        raise ValueError("BASELINE_AUDIT_ROOT_COUNT_MISMATCH")
    if root_names != ROOT_NAMES:
        raise ValueError("ROOT_AUDIT_NAMES_MISMATCH")
    if set(baseline_names) & set(root_names):
        raise ValueError("BASELINE_ROOT_AUDIT_OVERLAP")

    for relative in ["QUASI_FEFFERMAN_A.lean", "RootAudit.lean"]:
        code = lean_code((base / relative).read_text(encoding="utf-8"))
        if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", code):
            raise ValueError(f"UNAPPROVED_ROOT_PROOF_CONSTRUCTION:{relative}")

    lock = json.loads((base / "lake-manifest.json").read_text(encoding="utf-8"))
    locked = {p["name"]: p["rev"] for p in lock["packages"]}
    if locked != baseline["dependency_revisions"]:
        raise ValueError("DEPENDENCY_LOCK_MISMATCH")
    if locked.get("mathlib") != MATHLIB_REV:
        raise ValueError("MATHLIB_LOCK_MISMATCH")
    if (base / "lean-toolchain").read_text(encoding="utf-8").strip() != \
            "leanprover/lean4:v4.33.0":
        raise ValueError("TOOLCHAIN_FILE_MISMATCH")
    return root_manifest, baseline, baseline_names, root_names


def parser_self_test() -> None:
    name = "Fixture.exact_endpoint"
    good = (
        f"TYPE_BEGIN:{name}\n{name} : True\nTYPE_END:{name}\n"
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    )
    assert set(inspect_axioms(good, [name])[name]["axioms"]) == ALLOWED_AXIOMS
    for invalid in [
        good + good,
        good.replace("Quot.sound", "sorryAx"),
        good.replace("Quot.sound", "Custom.assumption"),
        good.replace("TYPE_END", "MISSING_END"),
        good + "error(lean.unknownIdentifier): failed\n",
    ]:
        try:
            inspect_axioms(invalid, [name])
        except ValueError:
            continue
        raise ValueError("AUDIT_PARSER_ACCEPTED_INVALID_FIXTURE")


def command(base: Path, args: list[str], log: Path) -> str:
    chunks: list[str] = []
    with log.open("w", encoding="utf-8", newline="\n") as output:
        process = subprocess.Popen(
            args,
            cwd=base,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        assert process.stdout is not None
        for line in process.stdout:
            chunks.append(line)
            output.write(line)
            output.flush()
            print(line, end="", flush=True)
        code = process.wait()
    if code:
        raise RuntimeError(f"COMMAND_FAILED:{args!r}:EXIT={code}")
    return "".join(chunks)


def external_audit(
    base: Path,
    root_manifest: dict,
    baseline: dict,
    baseline_names: list[str],
    root_names: list[str],
) -> None:
    if os.name != "nt":
        raise RuntimeError("EXTERNAL_NATIVE_WINDOWS_ONLY")

    evidence = base / "root-evidence"
    evidence.mkdir(exist_ok=True)
    manifest_bytes = (base / "root-manifest.json").read_bytes()
    initial_manifest_sha = hashlib.sha256(manifest_bytes).hexdigest()
    status: dict = {
        "root_status": "CONDITIONAL_FORMAL_CLOSURE",
        "marker": "!!!",
        "baseline_endpoint_status": "A_TIER",
        "root_theorem_status": "PENDING",
        "cache_policy": "MATHLIB_CACHE_AND_INCREMENTAL_LAKE",
        "root_manifest_sha256": initial_manifest_sha,
        "platform": platform.platform(),
        "physical_QFA_root_implication": True,
        "unconditional_closure": False,
        "execution": (
            "GITHUB_ACTIONS"
            if os.getenv("GITHUB_ACTIONS") == "true"
            else "EXTERNAL_NATIVE_WINDOWS"
        ),
        "unresolved_premises": root_manifest["unresolved_premises"],
    }

    def unchanged_snapshot() -> None:
        if digest(base / "root-manifest.json") != initial_manifest_sha:
            raise ValueError("ROOT_MANIFEST_CHANGED_DURING_EXTERNAL_RUN")
        inspect_sources(base)

    def dependency_snapshot(phase: str) -> None:
        for package, rev in baseline["dependency_revisions"].items():
            path = base / ".lake" / "packages" / package
            actual = command(
                base,
                ["git", "-C", str(path), "rev-parse", "HEAD"],
                evidence / f"{phase}-revision-{package}.txt",
            ).strip()
            if actual != rev:
                raise ValueError(f"DEPENDENCY_REVISION_MISMATCH:{package}")
            dirty = command(
                base,
                [
                    "git",
                    "-C",
                    str(path),
                    "status",
                    "--porcelain",
                    "--untracked-files=all",
                ],
                evidence / f"{phase}-status-{package}.txt",
            )
            if dirty.strip():
                raise ValueError(f"MODIFIED_DEPENDENCY_SOURCE:{package}")

    try:
        if os.getenv("GITHUB_ACTIONS") == "true":
            commit = command(
                base, ["git", "rev-parse", "HEAD"], evidence / "commit.txt"
            ).strip()
            if commit != os.environ["GITHUB_SHA"]:
                raise ValueError("GITHUB_CHECKOUT_COMMIT_MISMATCH")
            status["github"] = {
                key: os.environ.get(f"GITHUB_{key.upper()}", "")
                for key in [
                    "repository",
                    "sha",
                    "ref",
                    "workflow",
                    "workflow_ref",
                    "workflow_sha",
                    "run_id",
                    "run_attempt",
                ]
            }

        version = command(
            base, ["lake", "env", "lean", "--version"], evidence / "lean-version.txt"
        )
        if not re.search(r"version 4\.33\.0,", version):
            raise ValueError("EXTERNAL_COMPILER_VERSION_MISMATCH")
        status["compiler"] = version.strip()

        command(base, ["lake", "exe", "cache", "get"], evidence / "mathlib-cache.log")
        dependency_snapshot("before")
        unchanged_snapshot()

        (evidence / "cache-ready.json").write_text(
            json.dumps(
                {
                    "dependency_revisions": baseline["dependency_revisions"],
                    "root_manifest_sha256": initial_manifest_sha,
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )

        command(base, ["lake", "build", "QFA"], evidence / "build.log")
        unchanged_snapshot()

        baseline_log = command(
            base, ["lake", "env", "lean", "Audit.lean"], evidence / "baseline-axioms.log"
        )
        root_log = command(
            base, ["lake", "env", "lean", "RootAudit.lean"], evidence / "root-axioms.log"
        )
        status["baseline_declarations"] = inspect_axioms(
            baseline_log, baseline_names
        )
        status["root_declarations"] = inspect_axioms(root_log, root_names)
        unchanged_snapshot()
        dependency_snapshot("after")

        status["root_theorem_status"] = (
            "EXTERNAL_COMPILER_AND_EXACT_AXIOM_AUDIT_PASS"
        )
        status["declaration_counts"] = {
            "baseline": len(baseline_names),
            "new_root": len(root_names),
            "total_compiled_and_audited": len(baseline_names) + len(root_names),
        }
        print(
            "QFA_CONDITIONAL_FORMAL_CLOSURE_PASS;"
            " BASELINE_108_A_TIER; ROOT_LE109_LE112_A_TIER"
        )
    except Exception as error:
        status["root_theorem_status"] = "FAIL"
        status["error"] = str(error)
        raise
    finally:
        (evidence / "status.json").write_text(
            json.dumps(status, indent=2) + "\n", encoding="utf-8"
        )
        (evidence / "root-manifest.json").write_bytes(manifest_bytes)


def main() -> int:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--static", action="store_true")
    modes.add_argument("--external", action="store_true")
    args = parser.parse_args()

    base = Path(__file__).resolve().parents[1]
    parser_self_test()
    root_manifest, baseline, baseline_names, root_names = inspect_sources(base)
    if args.static:
        print(
            json.dumps(
                {
                    "source_inspection": "PASS",
                    "audit_parser_fixtures": "PASS",
                    "baseline_declarations": len(baseline_names),
                    "root_declarations": len(root_names),
                    "root_status": "CONDITIONAL_FORMAL_CLOSURE_CANDIDATE",
                    "local_lean_executions": 0,
                    "external_verification": "PENDING",
                }
            )
        )
    else:
        external_audit(
            base, root_manifest, baseline, baseline_names, root_names
        )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(f"QFA_ROOT_AUDIT_FAILURE:{exc}", file=sys.stderr)
        sys.exit(1)
