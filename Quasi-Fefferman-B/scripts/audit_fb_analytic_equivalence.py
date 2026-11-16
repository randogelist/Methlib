"""Compile and theorem-audit the Fefferman-B analytic equivalence triple."""

from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
UPGRADE = "QuasiFeffermanB.FeffermanBAnalyticUpgradeStatement"
DECLARATIONS = (
    "QuasiFeffermanB.FEFFERMAN_B_IFF_SPACE_OMEGA",
    "QuasiFeffermanB.FEFFERMAN_B_IFF_TIME_OMEGA",
    "QuasiFeffermanB.FEFFERMAN_B_IFF_SPACETIME_OMEGA",
    "QuasiFeffermanB.FEFFERMAN_B_ANALYTIC_EQUIVALENCE_TRIPLE",
)


def run(argv, cwd, env, log):
    with log.open("w", encoding="utf-8") as out:
        proc = subprocess.run(
            argv,
            cwd=cwd,
            env=env,
            stdout=out,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
        )
    return proc.returncode


def reports(text):
    found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    found += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", text)]
    result = {}
    for name, raw in found:
        raw = re.sub(r"\.\{[^{}]*\}", "", raw)
        result[name] = {item.strip() for item in raw.split(",") if item.strip()}
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", default=".")
    args = parser.parse_args()

    base = Path(args.package).resolve()
    root = base / "qfb"
    evidence = base / "evidence" / "fb-analytic-equivalence"
    evidence.mkdir(parents=True, exist_ok=True)

    version = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.33.0," not in version:
        raise ValueError(f"Wrong compiler: {version}")

    build = root / ".lake" / "build" / "lib" / "lean"
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    inherited = [p for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([
        str(build),
        str(base / ".lake" / "build" / "lib" / "lean"),
        *inherited,
    ])

    module = "QFBBridge.FeffermanBAnalyticVariants"
    source = root / "QFBBridge" / "FeffermanBAnalyticVariants.lean"
    target = build / (module.replace(".", "/") + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    build_log = evidence / "build.log"
    code = run(["lean", "-o", str(target), str(source)], root, env, build_log)
    if code:
        raise ValueError(f"Compilation failed for {module}")

    audit_log = evidence / "axioms.log"
    audit_source = root / "ci" / "FeffermanBAnalyticEquivalenceAudit.lean"
    code = run(["lean", str(audit_source)], root, env, audit_log)
    if code:
        raise ValueError("Analytic equivalence audit file failed to compile")

    text = audit_log.read_text(encoding="utf-8")
    if re.search(r"\bsorryAx\b|\buses ['`]sorry['`]|\berror(?:\([^\n)]*\))?:", text):
        raise ValueError("Lean error or sorry dependency")

    observed = reports(text)
    missing = [name for name in DECLARATIONS if name not in observed]
    if missing:
        raise ValueError(f"Missing theorem-level axiom reports: {missing}")

    declaration_status = {}
    for name in DECLARATIONS:
        axioms = observed[name]
        if not axioms <= STANDARD:
            raise ValueError(
                f"Unapproved theorem axioms for {name}: {sorted(axioms - STANDARD)}")
        if text.count(f"TYPE_BEGIN:{name}\n") != 1:
            raise ValueError(f"Missing type start marker for {name}")
        if text.count(f"TYPE_END:{name}\n") != 1:
            raise ValueError(f"Missing type end marker for {name}")
        declaration_status[name] = {
            "status": "A_TIER",
            "axioms": sorted(axioms),
        }

    status = {
        "status": "PASS",
        "lean": version.strip(),
        "module": module,
        "declarations": declaration_status,
        "formal_closure": {
            "status": "CONDITIONAL_FORMAL_CLOSURE",
            "root": DECLARATIONS[-1],
            "named_unresolved_premise": UPGRADE,
        },
        "local_lean_executions": 0,
    }
    (evidence / "status.json").write_text(
        json.dumps(status, indent=2) + "\n", encoding="utf-8")
    for name in DECLARATIONS:
        print(f"!=! DECLARATION {name}")
    print(f"!!! CONDITIONAL_FORMAL_CLOSURE {DECLARATIONS[-1]}")
    print(json.dumps(status, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print(f"FB_ANALYTIC_EQUIVALENCE_AUDIT_FAIL: {error}", file=sys.stderr)
        sys.exit(1)
