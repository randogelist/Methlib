#!/usr/bin/env python3
"""Create an isolated native-package overlay; never edit the inherited source."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil

TOOLCHAIN = "leanprover/lean4:v4.33.0"
MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"
EXPECTED_LAKEFILE_SHA256 = None  # Git source identity is recorded separately.


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--extension", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--reuse-native-cache", action="store_true")
    args = parser.parse_args()
    native, extension, output = (p.resolve() for p in
                                 (args.native, args.extension, args.output))
    if output == native or native in output.parents or output in native.parents:
        raise ValueError("output must be separate from inherited package")
    if extension == output or output in extension.parents:
        raise ValueError("output cannot contain or equal extension sources")
    if (native / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError("inherited toolchain is not the frozen compiler")
    manifest = json.loads((native / "lake-manifest.json").read_text())
    mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_REV:
        raise ValueError("inherited Mathlib revision differs from frozen pin")
    inherited = {p.relative_to(native).as_posix(): digest(p)
                 for p in sorted(native.rglob("*")) if p.is_file()
                 and not any(x in {".lake", "evidence", ".git", "__pycache__"}
                             for x in p.relative_to(native).parts)}
    output.mkdir(parents=True, exist_ok=True)
    # Keep already cached compiler objects on repeated external runs.
    shutil.copytree(native, output, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns(".lake", "evidence", ".git", "__pycache__"))
    namespace = extension / "SingularityDisprovement"
    if not namespace.is_dir():
        raise ValueError("new theorem namespace directory is missing")
    target_namespace = output / "SingularityDisprovement"
    if target_namespace.exists():
        shutil.rmtree(target_namespace)
    shutil.copytree(namespace, target_namespace)
    root_module = extension / "SingularityDisprovement.lean"
    if root_module.exists():
        shutil.copy2(root_module, output / root_module.name)
    else:
        # Named module builds work without an aggregate root; this root contains
        # no theorem and does not affect endpoint completeness.
        (output / "SingularityDisprovement.lean").write_text(
            "-- The endpoint manifest selects the independently audited modules.\n")
    target_ci = output / "ci_singularity"
    if target_ci.exists():
        shutil.rmtree(target_ci)
    shutil.copytree(extension / "ci", target_ci,
                    ignore=shutil.ignore_patterns("__pycache__"))
    config = output / "lakefile.toml"
    config.write_text(config.read_text() +
                      '\n[[lean_lib]]\nname = "SingularityDisprovement"\n'
                      'roots = ["SingularityDisprovement"]\n')
    if args.reuse_native_cache:
        for relative in (".lake/packages", ".lake/build"):
            source = native / relative
            if source.exists() and not (output / relative).exists():
                shutil.copytree(source, output / relative)
    evidence = output / "evidence"
    evidence.mkdir(exist_ok=True)
    (evidence / "inherited-source-hashes.json").write_text(
        json.dumps(inherited, indent=2, sort_keys=True) + "\n")
    (evidence / "lockfile-before.sha256").write_text(
        digest(output / "lake-manifest.json") + "  lake-manifest.json\n")
    for relative, expected in inherited.items():
        if digest(native / relative) != expected:
            raise ValueError("inherited source was changed: " + relative)
        if relative != "lakefile.toml" and digest(output / relative) != expected:
            raise ValueError("inherited overlay mismatch: " + relative)
    print(json.dumps({"status": "PASS", "output": str(output),
                      "native_source_mutations": 0, "inherited_files": len(inherited)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
