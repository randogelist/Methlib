"""External-only build/audit driver. Exact source signatures; no root inference."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from threading import Lock
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def source_fingerprints(manifest, modules, source_hashes):
    """Bind cached objects to their entire candidate import closure and native pins."""
    result, visiting = {}, set()
    native = {k: manifest[k] for k in ("foundation_sha", "lean", "mathlib")}
    def fingerprint(module):
        if module in result:
            return result[module]
        if module in visiting:
            raise ValueError("Cyclic candidate imports")
        visiting.add(module)
        spec = modules[module]
        payload = {"native": native, "module": module,
                   "source": source_hashes[spec["source"]],
                   "imports": {name: fingerprint(name) if name in modules else native
                               for name in sorted(spec["imports"])}}
        result[module] = hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()
        visiting.remove(module)
        return result[module]
    for module in sorted(modules):
        fingerprint(module)
    return result

def cached_object_matches(record, fingerprint, object_path):
    return (isinstance(record, dict) and record.get("fingerprint") == fingerprint and object_path.is_file()
            and record.get("olean_sha256") == hashlib.sha256(object_path.read_bytes()).hexdigest())

def check_log(text, names):
    if re.search(r"\bsorryAx\b|\buses ['`]sorry['`]|\berror(?:\([^\n)]*\))?:", text):
        raise ValueError("Lean error or sorry dependency")
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    observed = [n for n, _ in reports]
    if sorted(observed) != sorted(names):
        raise ValueError(f"Axiom declaration mismatch: {observed}")
    types = {}
    for name, raw in reports:
        # pp.universes annotates constants; these are level arguments, not names.
        raw_names = re.sub(r"\.\{[^{}]*\}", "", raw)
        axioms = {a.strip() for a in raw_names.split(",") if a.strip()}
        if not axioms <= ALLOWED:
            raise ValueError(f"Unapproved axioms for {name}: {sorted(axioms - ALLOWED)}")
        begin, end = f"TYPE_BEGIN:{name}\n", f"TYPE_END:{name}\n"
        if text.count(begin) != 1 or text.count(end) != 1:
            raise ValueError(f"Missing/duplicate type marker for {name}")
        statement = text.split(begin)[1].split(end)[0].strip()
        if not statement:
            raise ValueError(f"Missing compiler-emitted type for {name}")
        types[name] = {"type": statement, "axioms": sorted(axioms)}
    return types

def self_test():
    name = "Fixture.test"
    good = f"TYPE_BEGIN:{name}\nFixture.test : True\nTYPE_END:{name}\n'{name}' depends on axioms: [propext]\n"
    assert check_log(good, [name])[name]["axioms"] == ["propext"]
    universe_good = good.replace("[propext]", "[propext, Classical.choice.{u}, Quot.sound.{u}]")
    assert set(check_log(universe_good, [name])[name]["axioms"]) == ALLOWED
    prefix_other = good.replace(name, name + "_SCALED")
    assert len(check_log(good + prefix_other, [name, name + "_SCALED"])) == 2
    for bad in [good.replace("[propext]", "[sorryAx]"), good + good,
                good.replace("TYPE_END:", "MISSING:"), good + "error: failed\n",
                good + "error(lean.synthInstanceFailed): failed\n",
                good.replace("[propext]", "[Unapproved.assumption]"),
                good.replace("[propext]", "[Unapproved.assumption.{u}]")]:
        try:
            check_log(bad, [name])
        except ValueError:
            continue
        raise AssertionError("Audit accepted a deliberately invalid fixture")
    print("AUDIT_POLICY_TESTS_PASS")

def cache_self_test():
    m = {"foundation_sha": "f", "lean": "l", "mathlib": "m"}
    modules = {"A": {"source": "A.lean", "imports": ["Mathlib"]},
               "B": {"source": "B.lean", "imports": ["A"]},
               "C": {"source": "C.lean", "imports": []}}
    sources = {"A.lean": "a", "B.lean": "b", "C.lean": "c"}
    first = source_fingerprints(m, modules, sources)
    changed = source_fingerprints(m, modules, {**sources, "A.lean": "changed"})
    assert first["A"] != changed["A"] and first["B"] != changed["B"]
    assert first["C"] == changed["C"]
    pinned = source_fingerprints({**m, "mathlib": "changed"}, modules, sources)
    assert all(first[k] != pinned[k] for k in first)
    assert not cached_object_matches({}, first["A"], Path("nonexistent-object-fixture"))
    with tempfile.TemporaryDirectory() as fixture:
        obj = Path(fixture) / "A.olean"
        obj.write_bytes(b"object-fixture")
        record = {"fingerprint": first["A"], "olean_sha256": hashlib.sha256(obj.read_bytes()).hexdigest()}
        assert cached_object_matches(record, first["A"], obj)
        assert not cached_object_matches(record, changed["A"], obj)
        assert not cached_object_matches(None, first["A"], obj)
        obj.write_bytes(b"modified-fixture")
        assert not cached_object_matches(record, first["A"], obj)
        obj.unlink()
        assert not cached_object_matches(record, first["A"], obj)
    print("CACHE_DEPENDENCY_POLICY_TESTS_PASS")

def stripped_code(text):
    # Lean nested block comments and line comments are removed before token checks.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i): depth += 1; i += 2
        elif depth and text.startswith("-/", i): depth -= 1; i += 2
        elif depth: i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i); i = len(text) if j < 0 else j
        else: out.append(text[i]); i += 1
    if depth: raise ValueError("Unterminated Lean comment")
    return "".join(out)

def module_imports(code):
    """Read the bare import syntax used by this source snapshot; fail closed."""
    result = []
    for line in code.splitlines():
        if re.match(r"\s*(?:public|private|meta)(?:\s+(?:public|private|meta))*\s+import\b", line):
            raise ValueError("Unsupported annotated import syntax")
        match = re.match(r"^[ \t]*import\b(.*)$", line)
        if match is None:
            continue
        names = match.group(1).split()
        if not names or any(name in {"all", "meta"} or not re.fullmatch(
                r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", name)
                for name in names):
            raise ValueError(f"Unsupported import syntax: {line}")
        result.extend(names)
    return result

def selected_import_closure(modules, targets=None):
    """Return a deterministic dependency-first order, including every target."""
    for module, spec in modules.items():
        missing = [name for name in spec["imports"]
                   if (name == "QuasiFeffermanB" or name.startswith("QuasiFeffermanB."))
                   and name not in modules]
        if missing:
            raise ValueError(f"Unresolved candidate imports in {module}: {missing}")
    requested = sorted(modules) if targets is None else sorted(set(targets))
    if not requested or any(name not in modules for name in requested):
        raise ValueError(f"Unknown or empty target selection: {requested}")
    result, visiting, visited = [], set(), set()
    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise ValueError("Cyclic candidate imports")
        visiting.add(module)
        for name in sorted(set(modules[module]["imports"])):
            if name in modules:
                visit(name)
        visiting.remove(module)
        visited.add(module)
        result.append(module)
    for module in requested:
        visit(module)
    return result

def selection_self_test():
    modules = {"QuasiFeffermanB.A": {"imports": ["Mathlib"]},
               "QuasiFeffermanB.B": {"imports": ["QuasiFeffermanB.A"]},
               "QuasiFeffermanB.C": {"imports": []}}
    selected = selected_import_closure(modules, ["QuasiFeffermanB.B"])
    assert selected == ["QuasiFeffermanB.A", "QuasiFeffermanB.B"]
    assert len(selected_import_closure(modules)) == 3
    assert module_imports("import Mathlib QuasiFeffermanB.A\n") == ["Mathlib", "QuasiFeffermanB.A"]
    bad_calls = [lambda: selected_import_closure(modules, ["Missing"]),
                 lambda: selected_import_closure(modules, []),
                 lambda: selected_import_closure({**modules, "QuasiFeffermanB.D":
                     {"imports": ["QuasiFeffermanB.Missing"]}}, ["QuasiFeffermanB.B"]),
                 lambda: selected_import_closure({**modules, "QuasiFeffermanB.A":
                     {"imports": ["QuasiFeffermanB.B"]}}, ["QuasiFeffermanB.B"]),
                 lambda: module_imports("public import Mathlib"),
                 lambda: module_imports("public meta import QuasiFeffermanB.Missing"),
                 lambda: module_imports("import all Mathlib"),
                 lambda: module_imports("import")]
    for bad in bad_calls:
        try:
            bad()
        except ValueError:
            continue
        raise AssertionError("Selection accepted an incomplete or unsupported import graph")
    print("TARGET_CLOSURE_POLICY_TESTS_PASS")

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--package", default=".")
    p.add_argument("--jobs", type=int, default=1, help="Independent module processes per import frontier; exact audits remain mandatory")
    p.add_argument("--target", action="append", help="Audit this module and its complete candidate import closure; repeatable")
    p.add_argument("--plan-only", action="store_true", help="Print the source-verified preload plan; execute no compiler")
    p.add_argument("--project", help="Source overlay path, permitted only with --plan-only")
    args = p.parse_args()
    if args.jobs < 1 or args.jobs > 4:
        raise ValueError("--jobs must be between 1 and 4")
    if args.self_test:
        self_test(); cache_self_test(); selection_self_test(); return 0
    if args.project and not args.plan_only:
        raise ValueError("--project is permitted only for the compiler-free plan")
    base = Path(args.package).resolve()
    root = Path(args.project).resolve() if args.project else base / "qfb"
    evidence = base / "evidence" / "qfb"
    manifest = json.loads((root / "endpoint-manifest.json").read_text())
    if set(manifest["allowed_axioms"]) != ALLOWED:
        raise ValueError("Axiom policy mismatch")
    actual_sources = {f.relative_to(root).as_posix(): hashlib.sha256(f.read_bytes()).hexdigest()
                      for f in sorted((root / "QuasiFeffermanB").rglob("*.lean"))}
    if actual_sources != manifest["sources"]:
        raise ValueError("Source snapshot mismatch; refresh the committed manifest")
    modules = {}
    for path in actual_sources:
        code = stripped_code((root / path).read_text())
        if re.search(r"\b(?:sorry|admit|axiom)\b", code):
            raise ValueError(f"Forbidden proof token in {path}")
        module = path[:-5].replace("/", ".")
        imports = module_imports(code)
        modules[module] = {"source": path, "imports": imports}
    audit_specs = {m["module"]: m for m in manifest["modules"]}
    if len(audit_specs) != len(manifest["modules"]):
        raise ValueError("Duplicate audited module")
    if not audit_specs or not set(audit_specs) <= set(modules):
        raise ValueError("Empty or invalid module audit manifest")
    all_names = [n for m in audit_specs.values() for n in m["declarations"]]
    if len(all_names) != len(set(all_names)):
        raise ValueError("Duplicate audited declaration")
    for m, spec in audit_specs.items():
        if spec["source"] != modules[m]["source"]:
            raise ValueError(f"Module/source association mismatch: {m}")
        if spec["sha256"] != actual_sources[spec["source"]]:
            raise ValueError(f"Module digest mismatch: {m}")
    selected = selected_import_closure(modules, args.target)
    fingerprints = source_fingerprints(manifest, modules, actual_sources)
    scope = {"mode": "TARGET_IMPORT_CLOSURE" if args.target is not None else "ALL_CANDIDATES",
             "manifest_validation": "ALL_SOURCES",
             "targets": sorted(set(args.target)) if args.target is not None else [],
             "source_snapshot_modules": len(modules),
             "selected_modules": selected,
             "excluded_modules": sorted(set(modules) - set(selected)),
             "selected_audit_modules": sum(m in audit_specs for m in selected),
             "selected_declarations": sum(len(audit_specs[m]["declarations"])
                                          for m in selected if m in audit_specs)}
    modules = {m: modules[m] for m in selected}
    audit_specs = {m: spec for m, spec in audit_specs.items() if m in modules}
    native_imports = sorted({i for m in modules.values() for i in m["imports"]
                             if i not in modules})
    plan = {"schema": 1, "status": "SOURCE_PRELOAD_PLAN; NOT_COMPILER_EVIDENCE",
            "pins": {k: manifest[k] for k in ("foundation_sha", "lean", "mathlib")},
            "scope": scope, "native_imports": native_imports,
            "dependency_fingerprints": {m: fingerprints[m] for m in selected},
            "allowed_axioms": sorted(ALLOWED), "root_status": "PENDING",
            "local_lean_executions": 0}
    if args.plan_only:
        print(json.dumps(plan, indent=2))
        return 0
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / "preload-plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    (evidence / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    version = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.33.0," not in version:
        raise ValueError(f"Wrong compiler: {version}")
    (evidence / "lean-version.txt").write_text(version)
    build_dir = root / ".lake" / "build" / "lib" / "lean"
    build_dir.mkdir(parents=True, exist_ok=True)
    cache_manifest_path = build_dir / "qfb-verified-object-cache.json"
    try:
        object_cache = json.loads(cache_manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        object_cache = {}
    env = os.environ.copy()
    inherited = [str(Path(p).resolve()) for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([str(build_dir), str(base / ".lake/build/lib/lean"), *inherited])
    status = {"root_status": "PENDING", "endpoint_completion_inferred": False,
              "contract_status": manifest["contract_status"], "scope": scope,
              "modules": {}, "declarations": {},
              "scheduler": {"kind": "DEPENDENCY_FRONTIER", "jobs": args.jobs},
              "resolution_marker": "!=!"}
    output_lock = Lock()
    def emit(line):
        with output_lock:
            print(line, flush=True)
    def checkpoint():
        target = evidence / "status.json"
        temporary = evidence / "status.json.tmp"
        temporary.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        temporary.replace(target)
    def command(argv, cwd, logfile, command_env=None):
        with logfile.open("w", encoding="utf-8") as log:
            proc = subprocess.Popen(argv, cwd=cwd, env=command_env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, encoding="utf-8")
            assert proc.stdout is not None
            for line in proc.stdout:
                with output_lock:
                    print(line, end="", flush=True)
                log.write(line)
            return proc.wait()
    native_result = command(["lake", "build", *native_imports], base, evidence / "foundation-imports.log")
    if native_result:
        status["foundation_status"] = "FAIL"
        (evidence / "status.json").write_text(json.dumps(status, indent=2) + "\n")
        return 1
    status["foundation_status"] = "PASS"
    def compile_and_audit(module):
        # Every worker owns exactly one output and its independent log files.
        # Shared status/cache manifests are written only by the parent thread.
        stem = module.replace(".", "_")
        out = build_dir / (module.replace(".", "/") + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        record = object_cache.get(module, {})
        if not isinstance(record, dict):
            record = {}
        cache_hit = (record.get("compiler_version") == version.strip()
                     and cached_object_matches(record, fingerprints[module], out))
        if cache_hit:
            code = 0
            (evidence / f"{stem}-build.log").write_text(
                "CACHED_VERIFIED_OBJECT: exact source/import-closure/compiler fingerprint and object digest matched.\n",
                encoding="utf-8")
            emit(f"CACHED_VERIFIED_OBJECT {module}")
        else:
            code = command(["lean", "-o", str(out), modules[module]["source"]], root,
                           evidence / f"{stem}-build.log", env)
        if code:
            return module, {"build": "FAIL"}, {}, None
        if not cache_hit:
            record = {"fingerprint": fingerprints[module],
                "olean_sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
                "producer_run_id": os.environ.get("GITHUB_RUN_ID"),
                "producer_commit": os.environ.get("GITHUB_SHA"),
                "compiler_version": version.strip()}
        module_status = {"build": "PASS",
            "build_origin": "CACHED_VERIFIED_OBJECT" if cache_hit else "EXTERNAL_COMPILER",
            "dependency_fingerprint": fingerprints[module],
            "object_provenance": record}
        if module not in audit_specs:
            return module, module_status, {}, record
        names = audit_specs[module]["declarations"]
        audit_source = [f"import {module}", "set_option pp.universes false", "set_option pp.explicit false", ""]
        for name in names:
            audit_source += [f'#eval IO.println "TYPE_BEGIN:{name}"', f"#check @{name}",
                             f'#eval IO.println "TYPE_END:{name}"', f"#print axioms {name}", ""]
        audit_path = evidence / f"{stem}-audit.lean"
        audit_path.write_text("\n".join(audit_source), encoding="utf-8")
        log = evidence / f"{stem}-axioms.log"
        code = command(["lean", str(audit_path)], root, log, env)
        declarations = {}
        try:
            if code:
                raise ValueError(f"Audit compiler exit {code}")
            declarations = check_log(log.read_text(), names)
            for name, details in declarations.items():
                details.update({"source": audit_specs[module]["source"],
                                "source_sha256": audit_specs[module]["sha256"],
                                "type_rendering": "readable compiler presentation; pinned source is normative",
                                "type_prettyprinter_elisions": "⋯" in details["type"] or "..." in details["type"],
                                "status": "A_TIER_EXACT_DECLARATION", "contract_completion": False})
            module_status["audit"] = "PASS"
        except ValueError as error:
            declarations = {}
            module_status["audit"] = "FAIL"
            module_status["error"] = str(error)
        return module, module_status, declarations, record

    pending = set(modules)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending:
            ready = sorted(m for m in pending if not any(i in pending for i in modules[m]["imports"]))
            if not ready:
                raise ValueError("Cyclic QFB imports")
            runnable = []
            for module in ready:
                pending.remove(module)
                if any(status["modules"].get(i, {}).get("build") != "PASS"
                       for i in modules[module]["imports"] if i in modules):
                    status["modules"][module] = {"build": "BLOCKED_BY_DEPENDENCY"}
                else:
                    runnable.append(module)
            # Results are committed in sorted order. The whole frontier joins
            # before dependent declarations can be submitted to the compiler.
            for module, module_status, declarations, record in pool.map(compile_and_audit, runnable):
                status["modules"][module] = module_status
                if record is None:
                    object_cache.pop(module, None)
                else:
                    object_cache[module] = record
                cache_manifest_path.write_text(json.dumps(object_cache, indent=2) + "\n", encoding="utf-8")
                status["declarations"].update(declarations)
                for name in declarations:
                    emit(f"!=! DECLARATION {name}")
                checkpoint()
            checkpoint()
    passed = all(m.get("build") == "PASS" and (k not in audit_specs or m.get("audit") == "PASS")
                 for k, m in status["modules"].items())
    status["status"] = "PASS" if passed else "FAIL"
    (evidence / "status.json").write_text(json.dumps(status, indent=2) + "\n")
    print(json.dumps(status, indent=2), flush=True)
    return 0 if passed else 1

if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print(f"AUDIT_DRIVER_FAIL: {error}", file=sys.stderr)
        sys.exit(1)

