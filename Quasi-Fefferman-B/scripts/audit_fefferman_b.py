"""Compile and audit the QFB -> Fefferman-B conditional bridge."""

from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMED = "QuasiFeffermanB.QFB_ONE_RESTART_OVERLAP"
STRICT = "QuasiFeffermanB.FEFFERMAN_B_OF_QFB_ONE_RESTART_OVERLAP"
CONDITIONAL = "QuasiFeffermanB.FEFFERMAN_B_CONDITIONAL_CLOSURE"


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
    evidence = base / "evidence" / "fefferman-b"
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

    modules = [
        ("QFBBridge.FeffermanBClosure",
         root / "QFBBridge" / "FeffermanBClosure.lean"),
        ("QFBAdmissions.OneRestartOverlapAxiom",
         root / "QFBAdmissions" / "OneRestartOverlapAxiom.lean"),
    ]
    module_status = {}
    for module, source in modules:
        target = build / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        log = evidence / (module.replace(".", "_") + "-build.log")
        code = run(["lean", "-o", str(target), str(source)], root, env, log)
        module_status[module] = "PASS" if code == 0 else "FAIL"
        if code:
            raise ValueError(f"Compilation failed for {module}")

    audit_log = evidence / "axioms.log"
    code = run(
        ["lean", str(root / "ci" / "FeffermanBClosureAudit.lean")],
        root,
        env,
        audit_log,
    )
    if code:
        raise ValueError("Conditional closure audit file failed to compile")

    text = audit_log.read_text(encoding="utf-8")
    if re.search(r"\bsorryAx\b|\buses ['`]sorry['`]|\berror(?:\([^\n)]*\))?:", text):
        raise ValueError("Lean error or sorry dependency")

    observed = reports(text)
    if STRICT not in observed or CONDITIONAL not in observed:
        raise ValueError(f"Missing theorem-level axiom reports: {sorted(observed)}")

    strict_axioms = observed[STRICT]
    conditional_axioms = observed[CONDITIONAL]
    if not strict_axioms <= STANDARD:
        raise ValueError(
            f"Unapproved strict theorem axioms: {sorted(strict_axioms - STANDARD)}")
    if NAMED not in conditional_axioms:
        raise ValueError("Conditional theorem does not expose the named overlap axiom")
    if not conditional_axioms <= STANDARD | {NAMED}:
        raise ValueError(
            "Unexpected conditional theorem axioms: "
            f"{sorted(conditional_axioms - (STANDARD | {NAMED}))}")

    for name in (STRICT, CONDITIONAL):
        if text.count(f"TYPE_BEGIN:{name}\n") != 1:
            raise ValueError(f"Missing type start marker for {name}")
        if text.count(f"TYPE_END:{name}\n") != 1:
            raise ValueError(f"Missing type end marker for {name}")

    status = {
        "status": "PASS",
        "lean": version.strip(),
        "modules": module_status,
        "strict_implication": {
            "declaration": STRICT,
            "status": "A_TIER",
            "axioms": sorted(strict_axioms),
        },
        "conditional_closure": {
            "declaration": CONDITIONAL,
            "status": "CONDITIONAL_FORMAL_CLOSURE",
            "named_unresolved_axiom": NAMED,
            "axioms": sorted(conditional_axioms),
        },
        "local_lean_executions": 0,
    }
    (evidence / "status.json").write_text(
        json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(f"!=! DECLARATION {STRICT}")
    print(f"!!! CONDITIONAL_FORMAL_CLOSURE {CONDITIONAL}")
    print(json.dumps(status, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print(f"FEFFERMAN_B_AUDIT_FAIL: {error}", file=sys.stderr)
        sys.exit(1)
