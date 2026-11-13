"""External-only build/audit driver. Exact source signatures; no root inference."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

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
    return (record.get("fingerprint") == fingerprint and object_path.is_file()
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

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--package", default=".")
    args = p.parse_args()
    if args.self_test:
        self_test(); cache_self_test(); return 0
    base = Path(args.package).resolve()
    root = base / "qfb"
    evidence = base / "evidence" / "qfb"
    evidence.mkdir(parents=True, exist_ok=True)
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
        imports = re.findall(r"^import\s+([^\s]+)", code, re.M)
        modules[module] = {"source": path, "imports": imports}
    audit_specs = {m["module"]: m for m in manifest["modules"]}
    if not audit_specs or not set(audit_specs) <= set(modules):
        raise ValueError("Empty or invalid module audit manifest")
    all_names = [n for m in audit_specs.values() for n in m["declarations"]]
    if len(all_names) != len(set(all_names)):
        raise ValueError("Duplicate audited declaration")
    for m, spec in audit_specs.items():
        if spec["sha256"] != actual_sources[spec["source"]]:
            raise ValueError(f"Module digest mismatch: {m}")
    (evidence / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    version = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.33.0," not in version:
        raise ValueError(f"Wrong compiler: {version}")
    (evidence / "lean-version.txt").write_text(version)
    build_dir = root / ".lake" / "build" / "lib" / "lean"
    build_dir.mkdir(parents=True, exist_ok=True)
    fingerprints = source_fingerprints(manifest, modules, actual_sources)
    cache_manifest_path = build_dir / "qfb-verified-object-cache.json"
    try:
        object_cache = json.loads(cache_manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        object_cache = {}
    env = os.environ.copy()
    inherited = [str(Path(p).resolve()) for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([str(build_dir), str(base / ".lake/build/lib/lean"), *inherited])
    status = {"root_status": "PENDING", "endpoint_completion_inferred": False,
              "contract_status": manifest["contract_status"], "modules": {}, "declarations": {}}
    def command(argv, cwd, logfile, command_env=None):
        with logfile.open("w", encoding="utf-8") as log:
            proc = subprocess.Popen(argv, cwd=cwd, env=command_env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, encoding="utf-8")
            assert proc.stdout is not None
            for line in proc.stdout:
                print(line, end="", flush=True); log.write(line)
            return proc.wait()
    native_imports = sorted({i for m in modules.values() for i in m["imports"]
                             if not i.startswith("QuasiFeffermanB.")})
    native_result = command(["lake", "build", *native_imports], base, evidence / "foundation-imports.log")
    if native_result:
        status["foundation_status"] = "FAIL"
        (evidence / "status.json").write_text(json.dumps(status, indent=2) + "\n")
        return 1
    status["foundation_status"] = "PASS"
    pending = set(modules)
    while pending:
        ready = sorted(m for m in pending if not any(i in pending for i in modules[m]["imports"]))
        if not ready: raise ValueError("Cyclic QFB imports")
        for module in ready:
            pending.remove(module)
            stem = module.replace(".", "_")
            if any(status["modules"].get(i, {}).get("build") != "PASS"
                   for i in modules[module]["imports"] if i in modules):
                status["modules"][module] = {"build": "BLOCKED_BY_DEPENDENCY"}; continue
            out = build_dir / (module.replace(".", "/") + ".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            cache_hit = cached_object_matches(object_cache.get(module, {}), fingerprints[module], out)
            if cache_hit:
                code = 0
                (evidence / f"{stem}-build.log").write_text(
                    "CACHED_VERIFIED_OBJECT: exact source/import-closure/compiler fingerprint and object digest matched.\n",
                    encoding="utf-8")
                print(f"CACHED_VERIFIED_OBJECT {module}", flush=True)
            else:
                object_cache.pop(module, None)
                code = command(["lean", "-o", str(out), modules[module]["source"]], root,
                               evidence / f"{stem}-build.log", env)
            if code:
                status["modules"][module] = {"build": "FAIL"}; continue
            if not cache_hit:
                object_cache[module] = {"fingerprint": fingerprints[module],
                    "olean_sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
                    "producer_run_id": os.environ.get("GITHUB_RUN_ID"),
                    "producer_commit": os.environ.get("GITHUB_SHA"),
                    "compiler_version": version.strip()}
            cache_manifest_path.write_text(json.dumps(object_cache, indent=2) + "\n", encoding="utf-8")
            status["modules"][module] = {"build": "PASS",
                "build_origin": "CACHED_VERIFIED_OBJECT" if cache_hit else "EXTERNAL_COMPILER",
                "dependency_fingerprint": fingerprints[module],
                "object_provenance": object_cache[module]}
            if module not in audit_specs: continue
            names = audit_specs[module]["declarations"]
            audit_source = [f"import {module}", "set_option pp.universes false", "set_option pp.explicit false", ""]
            for name in names:
                audit_source += [f'#eval IO.println "TYPE_BEGIN:{name}"', f"#check @{name}",
                                 f'#eval IO.println "TYPE_END:{name}"', f"#print axioms {name}", ""]
            audit_path = evidence / f"{stem}-audit.lean"
            audit_path.write_text("\n".join(audit_source), encoding="utf-8")
            log = evidence / f"{stem}-axioms.log"
            code = command(["lean", str(audit_path)], root, log, env)
            try:
                if code: raise ValueError(f"Audit compiler exit {code}")
                declarations = check_log(log.read_text(), names)
                for name, details in declarations.items():
                    details.update({"source": audit_specs[module]["source"],
                                    "source_sha256": audit_specs[module]["sha256"],
                                    "type_rendering": "readable compiler presentation; pinned source is normative",
                                    "type_prettyprinter_elisions": "⋯" in details["type"] or "..." in details["type"],
                                    "status": "A_TIER_EXACT_DECLARATION", "contract_completion": False})
                    status["declarations"][name] = details
                    print(f"!=! DECLARATION {name}", flush=True)
                status["modules"][module]["audit"] = "PASS"
            except ValueError as error:
                status["modules"][module]["audit"] = "FAIL"
                status["modules"][module]["error"] = str(error)
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

