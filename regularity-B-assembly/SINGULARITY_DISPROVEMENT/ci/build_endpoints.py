#!/usr/bin/env python3
"""External compiler driver: independently build/audit exact endpoint contracts."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from check_endpoint_audit import audit
from check_extension_sources import check as check_sources

REQUIRED = [f"R{i:02d}" for i in range(1, 13)]
STATE_PATH = Path("evidence/endpoint-status.json")
EXPECTED_MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"


def write_state(state: dict) -> None:
    STATE_PATH.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run(command: list[str], log: Path) -> tuple[bool, str]:
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w", encoding="utf-8") as stream:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, encoding="utf-8", errors="replace", bufsize=1)
        for line in process.stdout:
            stream.write(line)
            print(line, end="", flush=True)
        success = process.wait() == 0
    return success, log.read_text(encoding="utf-8")


def load_plan() -> tuple[list[dict], list[str]]:
    plan = json.loads(Path("ci_singularity/endpoints.json").read_text(encoding="utf-8"))
    if plan.get("schema_version") != 1:
        raise ValueError("unsupported endpoint manifest schema")
    records = plan.get("endpoints")
    if not isinstance(records, list) or not records:
        raise ValueError("nonempty explicit endpoint manifest required")
    ids, names = set(), set()
    for record in records:
        identity = record.get("id")
        if identity not in REQUIRED or identity in ids:
            raise ValueError("invalid/duplicate endpoint ID: " + repr(identity))
        ids.add(identity)
        name, module = record.get("name"), record.get("module")
        for value in (name, module):
            if not isinstance(value, str) or not re.fullmatch(
                    r"SingularityDisprovement\.[A-Za-z_][A-Za-z0-9_.]*", value):
                raise ValueError("invalid native endpoint declaration/module: " + repr(value))
        if name in names:
            raise ValueError("same theorem registered for multiple endpoint contracts")
        names.add(name)
        audit_path = Path(record.get("audit", ""))
        if audit_path.is_absolute() or ".." in audit_path.parts:
            raise ValueError("audit path must remain inside extension CI directory")
        if len(audit_path.parts) < 2 or audit_path.parts[0] != "ci":
            raise ValueError("audit path must be ci/endpoint_audits/<id>.lean")
        if audit_path.suffix != ".lean":
            raise ValueError("audit must be a Lean source")
    helpers = plan.get("helper_modules", [])
    if not isinstance(helpers, list) or len(helpers) != len(set(helpers)):
        raise ValueError("helper modules must be a duplicate-free list")
    for module in helpers:
        if not isinstance(module, str) or not re.fullmatch(
                r"SingularityDisprovement\.[A-Za-z_][A-Za-z0-9_.]*", module):
            raise ValueError("invalid helper module: " + repr(module))
    return sorted(records, key=lambda item: item["id"]), helpers


def main() -> int:
    Path("evidence").mkdir(exist_ok=True)
    state = {"schema_version": 1, "status": "FAIL", "marker": "!=!",
             "source_sha": os.environ.get("GITHUB_SHA"),
             "required_ids": REQUIRED, "resolved_ids": [],
             "helper_builds": {},
             "endpoints": {identity: {"status": "PENDING"} for identity in REQUIRED},
             "errors": []}
    write_state(state)
    if os.environ.get("SINGULARITY_EXTERNAL_COMPILER") != "1":
        state["errors"].append("external compiler environment flag not set; no compiler executed")
        write_state(state)
        print(json.dumps(state), flush=True)
        return 1
    try:
        records, helpers = load_plan()
        policy = check_sources(Path.cwd())
        Path("evidence/extension-sources.json").write_text(json.dumps(policy, indent=2) + "\n")
        if policy["status"] != "PASS":
            raise ValueError("source policy failed: " + repr(policy["errors"]))
        ok, version = run(["lean", "--version"], Path("evidence/lean-version.txt"))
        if not ok or "version 4.33.0," not in version:
            raise ValueError("external compiler differs from frozen Lean 4.33.0")
        ok, revision = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                           Path("evidence/mathlib-revision.txt"))
        if not ok or revision.strip() != EXPECTED_MATHLIB:
            raise ValueError("external Mathlib differs from frozen source revision")
        before = Path("evidence/lockfile-before.sha256").read_text().split()[0]
        if hashlib.sha256(Path("lake-manifest.json").read_bytes()).hexdigest() != before:
            raise ValueError("dependency manifest changed after overlay preparation")
        build_results = {}
        for module in helpers:
            source = Path(module.replace(".", "/") + ".lean")
            if not source.exists():
                state["helper_builds"][module] = "PENDING"
                write_state(state)
                continue
            ok, _ = run(["lake", "build", module],
                        Path("evidence", module + "-helper-build.log"))
            build_results[module] = ok
            state["helper_builds"][module] = "PASS" if ok else "FAIL"
            # Helper compilation carries no endpoint A_TIER promotion.
            write_state(state)
        for record in records:
            identity, name, module = (record[key] for key in ("id", "name", "module"))
            result = dict(record, status="PENDING", build="NOT_RUN", audit_result="NOT_RUN")
            state["endpoints"][identity] = result
            source = Path(module.replace(".", "/") + ".lean")
            audit_path = Path("ci_singularity", *Path(record["audit"]).parts[1:])
            if not source.exists() or not audit_path.exists():
                result["reason"] = "module or exact-signature audit source not yet supplied"
                write_state(state)
                continue
            audit_source = audit_path.read_text(encoding="utf-8")
            if ("EXACT_TYPE_PASS:" + name not in audit_source or
                    "#print axioms " + name not in audit_source or
                    not re.search(r"\bexample\b", audit_source)):
                result.update(status="FAIL", reason="exact-signature audit source incomplete")
                write_state(state)
                continue
            if module not in build_results:
                ok, _ = run(["lake", "build", module],
                            Path("evidence", module + "-build.log"))
                build_results[module] = ok
            result["build"] = "PASS" if build_results[module] else "FAIL"
            if not build_results[module]:
                result["status"] = "FAIL"
                write_state(state)
                continue
            ok, transcript = run(["lake", "env", "lean", str(audit_path)],
                                 Path("evidence", identity + "-axioms.log"))
            checked = audit(transcript, name)
            Path("evidence", identity + "-audit.json").write_text(
                json.dumps(checked, indent=2) + "\n", encoding="utf-8")
            result["audit_result"] = checked["status"] if ok else "FAIL"
            if ok and checked["status"] == "PASS":
                result.update(status="A_TIER", marker="!=!", axioms=checked["axioms"])
                state["resolved_ids"].append(identity)
                print("!=! " + identity + " " + name, flush=True)
            else:
                result.update(status="FAIL", errors=checked["errors"])
            write_state(state)
        resolved = set(state["resolved_ids"])
        state["status"] = "PASS" if resolved == set(REQUIRED) else "PARTIAL"
        state["resolved_count"] = len(resolved)
        state["pending_ids"] = [identity for identity in REQUIRED if identity not in resolved]
    except (OSError, ValueError, TypeError, KeyError) as error:
        state["errors"].append(str(error))
    write_state(state)
    print(json.dumps(state, indent=2), flush=True)
    return 0 if state["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
