#!/usr/bin/env python3
"""Derive an audited, dependency-closed source lane from a verified full plan.

This does not execute Lean. Run only after the full plan/manifest check passes.
Each output source is copied byte-for-byte and the resulting subset receives
its own source manifest. A lane does not establish coverage of other lanes.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOTS = {
    "fubini_swap_candidate": "HVRPrimeGridSwapDirect",
    "fubini_bridge": "HVRPrimeFiniteFrequencyDirect",
    "fubini_right_candidate": "HVRPrimeRightCompactSupport",
    "fubini_left_candidate": "HVRPrimeLeftFull",
    "fubini_exp_candidate": "HVRComplexExpIntegralDirect",
    "fubini_candidates": "HVRFubiniCandidateLane",
    "fubini_right": "HVRPrimeGridIntegrability",
    "snd": "HVRPrimeSndAssembly",
    "matrix": "HVRPrimeGramJacobiBridge",
    "frequency": "HVRZetaHyperbolicFiniteFrequency",
    "modes": "HVR_PrimeMellin_Modes",
    "assembly": "HVR_PrimeMellin_ModeAssembly",
    "bounds": "HVRZetaHyperbolicFrequencyBounds",
    "moment": "HVRPrimeWeightedMoment",
    "primefreq": "HVRPrimeLaplaceFrequencyBounds",
    "quadrature": "HVRPrimeWeightedFrequencyApproximation",
    "cell": "HVRFrequencyCellError",
    "cells": "HVRFrequencyFiniteCells",
    "root": "HVR_PrimeDensity_FinalRoot",
}
IMPORT_LINE = re.compile(r"^\s*(?:(?:public|meta)\s+)*import\s+([^\n-]+)")
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.]*$")


def checksum(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lane", choices=ROOTS, required=True)
    args = parser.parse_args()
    pkg, out = args.package.resolve(strict=True), args.output.resolve()
    if out == pkg or pkg in out.parents or out in pkg.parents:
        raise ValueError("output must be separate from input package")
    # Do not trust a plan subset unless the committed full plan was checked.
    subprocess.run([sys.executable, str(pkg / "run_linux.py"), "--check-plan"], check=True)
    original_plan = json.loads((pkg / "plan.json").read_text(encoding="utf-8"))
    by_name = {entry["module"]: entry for entry in original_plan}
    if len(by_name) != len(original_plan):
        raise ValueError("duplicate module in full plan")

    def imports(module):
        path = pkg / "sources" / (module + ".lean")
        for line in path.read_text(encoding="utf-8").splitlines():
            match = IMPORT_LINE.match(line)
            if not match:
                continue
            for token in match.group(1).split():
                if not MODULE.fullmatch(token):
                    raise ValueError("unrecognized import token " + token)
                if token in by_name:
                    yield token
                elif token.startswith(("HVR", "PrimeSpectral", "NativeFubini")):
                    raise ValueError(f"unknown local import {module} -> {token}")

    visited, active = set(), set()
    def visit(module):
        if module in visited:
            return
        if module in active:
            raise ValueError("cyclic import at " + module)
        if module not in by_name:
            raise ValueError("missing lane root " + module)
        active.add(module)
        for dependency in imports(module):
            visit(dependency)
        active.remove(module)
        visited.add(module)

    root = ROOTS[args.lane]
    visit(root)
    # The root no longer imports the historical Abel helper, but the separate
    # diagnostic traces that helper as a control. Compile it without
    # introducing a dependency into the root theorem.
    if args.lane == "root":
        visit("HVR_PrimeMellin_Abel")
    if args.lane == "fubini_bridge":
        visit("HVRPrimeWeightedFrequencyApproximation")
    if args.lane == "fubini_exp_candidate":
        visit("HVR_Complex_PoleLaplace")
    subset = [entry for entry in original_plan if entry["module"] in visited]
    installed = set()
    for entry in subset:
        module = entry["module"]
        missing = set(imports(module)) - installed
        if missing:
            raise ValueError(f"plan is not topological for {module}: {sorted(missing)}")
        installed.add(module)
    if not by_name[root]["theorems"]:
        raise ValueError("root has no named theorem audits")
    if out.exists():
        raise ValueError("refusing to overwrite output")
    (out / "sources").mkdir(parents=True)
    for entry in subset:
        name = entry["module"] + ".lean"
        source, dest = pkg / "sources" / name, out / "sources" / name
        shutil.copyfile(source, dest)
        if checksum(source) != checksum(dest):
            raise ValueError("copy mismatch for " + name)
    for name in ("run_linux.py", "freeze_manifest.py"):
        shutil.copyfile(pkg / name, out / name)
    (out / "plan.json").write_text(json.dumps(subset, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(out / "freeze_manifest.py")], cwd=out, check=True)
    subprocess.run([sys.executable, str(out / "run_linux.py"), "--check-plan"], cwd=out, check=True)
    (out / "full_manifest.sha256").write_text(
        checksum(pkg / "sources.sha256") + "  sources.sha256\n", encoding="utf-8")
    print("LANE=" + args.lane)
    print("ROOT=" + root)
    print("FULL_PLAN_SHA256=" + checksum(pkg / "plan.json"))
    print("FULL_MANIFEST_SHA256=" + checksum(pkg / "sources.sha256"))
    print("MODULES=" + str(len(subset)))
    print("NAMED_THEOREMS=" + str(sum(len(x["theorems"]) for x in subset)))
    print("PROJECT_SOURCES_COPIED_BYTE_EXACT=YES")
    print("SEMANTIC_INDEPENDENCE=NOT_ESTABLISHED")

if __name__ == "__main__":
    main()
