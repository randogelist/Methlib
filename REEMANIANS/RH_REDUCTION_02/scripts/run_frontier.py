#!/usr/bin/env python3
"""Cached native Windows Lean runner. This file never downloads dependencies."""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any

PACKAGE_ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXTERNAL_PREFIXES = {"Init", "Lean", "Std", "Lake", "Mathlib", "Aesop", "Batteries",
                     "Qq", "ProofWidgets", "LeanSearchClient", "ImportGraph", "Plausible", "Cli"}
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
VERSION_RE = re.compile(r"Lean \(version ([^, )]+)")
AUDIT_RE = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)
BAD_PROOF_RE = re.compile(r"\bsorryAx\b|declaration uses ['\u2018]sorry['\u2019]")


class RunnerError(RuntimeError):
    pass


def emit(key: str, value: Any) -> None:
    print(f"{key}={value}", flush=True)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def stable_hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def safe_relative(root: Path, name: str) -> Path:
    p = (root / name).resolve()
    try:
        p.relative_to(root.resolve())
    except ValueError as exc:
        raise RunnerError(f"PATH_OUTSIDE_PACKAGE|{name}") from exc
    return p


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temp.replace(path)


def strip_comments(text: str) -> str:
    """Remove Lean comments/strings while preserving line positions."""
    out: list[str] = []
    i, depth = 0, 0
    in_string = False
    while i < len(text):
        c = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            j = text.find("\n", i)
            if j < 0:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (j - i))
            i = j
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def imports_of(path: Path) -> list[str]:
    result: list[str] = []
    for line in strip_comments(read_text(path)).splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", line)
        if not match:
            continue
        for name in match.group(1).split():
            if not MODULE_RE.fullmatch(name):
                raise RunnerError(f"UNSUPPORTED_IMPORT_SYNTAX|{path}|{name}")
            if name not in result:
                result.append(name)
    return result


@dataclass(frozen=True)
class Module:
    name: str
    source: Path
    source_root: Path
    imports: tuple[str, ...]
    source_hash: str
    backend: bool


def module_relative(name: str, suffix: str) -> Path:
    if not MODULE_RE.fullmatch(name):
        raise RunnerError(f"INVALID_MODULE_NAME|{name}")
    return Path(*name.split(".")).with_suffix(suffix)


def load_config(root: Path, override: Path | None = None) -> dict[str, Any]:
    path = override or root / "scripts" / "build_config.json"
    if not path.is_file():
        raise RunnerError(f"BUILD_CONFIG_MISSING|{path}")
    cfg = json.loads(read_text(path))
    if cfg.get("toolchain") != "4.33.0":
        raise RunnerError("BUILD_CONFIG_TOOLCHAIN_MUST_BE_4.33.0")
    if not cfg.get("package") or not cfg.get("targets"):
        raise RunnerError("BUILD_CONFIG_PACKAGE_OR_TARGETS_MISSING")
    audits = cfg.get("audit_modules")
    if not isinstance(audits, list) or not audits:
        raise RunnerError("BUILD_CONFIG_AUDITS_MISSING")
    for audit in audits:
        if not audit.get("module") or not audit.get("theorems"):
            raise RunnerError("BUILD_CONFIG_EMPTY_AUDIT")
        for name in audit["theorems"]:
            if not MODULE_RE.fullmatch(name):
                raise RunnerError(f"INVALID_AUDIT_THEOREM|{name}")
    for control in cfg.get("negative_controls", []):
        if not control.get("file") or not control.get("expected_fragments"):
            raise RunnerError("BUILD_CONFIG_INVALID_NEGATIVE_CONTROL")
        safe_relative(root, control["file"])
    rh_theorem = cfg.get("rh_theorem")
    if rh_theorem is not None:
        if not isinstance(rh_theorem, str) or not MODULE_RE.fullmatch(rh_theorem):
            raise RunnerError("INVALID_RH_THEOREM_NAME")
        audited = {name for audit in audits for name in audit["theorems"]}
        if rh_theorem not in audited:
            raise RunnerError("RH_THEOREM_NOT_EXPLICITLY_AUDITED")
    return cfg


def verify_manifest(root: Path, manifest: Path | None = None) -> dict[str, str]:
    path = manifest or root / "source-manifest.json"
    if not path.is_file():
        raise RunnerError("SOURCE_MANIFEST_MISSING")
    data = json.loads(read_text(path))
    entries = data.get("files")
    if not isinstance(entries, dict) or not entries:
        raise RunnerError("SOURCE_MANIFEST_EMPTY")
    for relative, digest in entries.items():
        source = safe_relative(root, relative)
        if not source.is_file() or not re.fullmatch(r"[a-f0-9]{64}", str(digest)):
            raise RunnerError(f"SOURCE_MANIFEST_INVALID_ENTRY|{relative}")
        if sha256(source) != digest:
            raise RunnerError(f"SOURCE_MANIFEST_MISMATCH|{relative}")
    ignored = {"_build", "_evidence", "_submission", "__pycache__", ".git"}
    required_suffixes = {".lean", ".py", ".cmd", ".json"}
    for source in root.rglob("*"):
        if not source.is_file() or any(part in ignored for part in source.relative_to(root).parts):
            continue
        relative = source.relative_to(root).as_posix()
        if source.resolve() == path.resolve():
            continue
        if source.suffix.lower() in required_suffixes and relative not in entries:
            raise RunnerError(f"UNMANIFESTED_SOURCE|{relative}")
    return entries


def build_graph(root: Path, cfg: dict[str, Any]) -> tuple[dict[str, Module], list[str]]:
    source_roots = [Path(p).resolve() if Path(p).is_absolute() else safe_relative(root, p)
                    for p in cfg.get("source_roots", [".", "backend"])]
    modules: dict[str, Module] = {}
    external: set[str] = set()
    state: dict[str, int] = {}

    def locate(name: str) -> tuple[Path, Path] | None:
        relative = module_relative(name, ".lean")
        found = [(r / relative, r) for r in source_roots if (r / relative).is_file()]
        if len(found) > 1:
            hashes = {sha256(p) for p, _ in found}
            if len(hashes) > 1:
                raise RunnerError(f"AMBIGUOUS_MODULE_SOURCE|{name}")
        return found[0] if found else None

    def visit(name: str) -> None:
        if state.get(name) == 2:
            return
        if state.get(name) == 1:
            raise RunnerError(f"IMPORT_CYCLE|{name}")
        found = locate(name)
        if not found:
            external.add(name)
            return
        path, source_root = found
        state[name] = 1
        dependencies = tuple(imports_of(path))
        for dep in dependencies:
            visit(dep)
        backend = source_root != root and source_root.name == "backend"
        modules[name] = Module(name, path, source_root, dependencies, sha256(path), backend)
        state[name] = 2

    targets = list(cfg["targets"]) + [a["module"] for a in cfg["audit_modules"]]
    for name in targets:
        if not locate(name):
            raise RunnerError(f"TARGET_SOURCE_MISSING|{name}")
        visit(name)
    for control in cfg.get("negative_controls", []):
        path = safe_relative(root, control["file"])
        if not path.is_file():
            raise RunnerError(f"NEGATIVE_SOURCE_MISSING|{path}")
        for dep in imports_of(path):
            visit(dep)
    allowed_external = EXTERNAL_PREFIXES | set(cfg.get("allowed_external_prefixes", []))
    for name in external:
        if name.split(".", 1)[0] not in allowed_external:
            raise RunnerError(f"UNBUNDLED_CUSTOM_DEPENDENCY|{name}")
    return modules, sorted(external)


def unique_paths(paths: list[Path]) -> list[Path]:
    seen: set[str] = set()
    result: list[Path] = []
    for path in paths:
        key = os.path.normcase(str(path.resolve()))
        if path.is_dir() and key not in seen:
            seen.add(key)
            result.append(path.resolve())
    return result


def cache_bases(root: Path) -> list[Path]:
    home = Path(os.environ.get("USERPROFILE", str(Path.home())))
    downloads = home / "Downloads"
    bases: list[Path] = []
    for key in ("MATHLIB_CACHE_ROOT", "LEAN_CACHE_ROOTS", "RH_CACHE_ROOTS", "HXY_BASE"):
        for item in os.environ.get(key, "").split(os.pathsep):
            if item:
                bases.append(Path(item))
    bases.extend([
        home / "lean-native" / "awpi_phi_rh_lean_sieved_v0_1_1",
        home / "lean-native",
    ])
    if downloads.is_dir():
        allowed = ("RH_", "HXY_", "C_SEARCH_", "AWPI", "awpi", "KTHETA_", "mathlib")
        for p in sorted(downloads.iterdir(), key=lambda x: x.name, reverse=True):
            if p.is_dir() and p.name.startswith(allowed) and p.resolve() != root:
                bases.append(p)
    expanded = list(bases)
    for base in bases:
        if not base.is_dir():
            continue
        # One nested package directory is common after archive extraction.
        try:
            for child in base.iterdir():
                if child.is_dir() and (
                    (child / "lean-toolchain").is_file()
                    or (child / "RH_HilbertLimit").is_dir()
                    or (child / ".lake" / "build" / "lib" / "lean").is_dir()
                ):
                    expanded.append(child)
        except OSError:
            continue
    return unique_paths(expanded)


def cache_library_paths(bases: list[Path]) -> list[Path]:
    paths: list[Path] = []
    for base in bases:
        paths.extend([
            base,
            base / "_build" / "lib" / "lean",
            base / ".lake" / "build" / "lib" / "lean",
            base / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean",
            base / "mathlib" / ".lake" / "build" / "lib" / "lean",
            base / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean",
        ])
        for package_dir in (
            base / ".lake" / "packages",
            base / "mathlib" / ".lake" / "packages",
            base / "packages",
        ):
            if package_dir.is_dir():
                try:
                    paths.extend(p / ".lake" / "build" / "lib" / "lean"
                                 for p in package_dir.iterdir() if p.is_dir())
                except OSError:
                    pass
    # Only directories containing olean files or known module directories matter.
    return [p for p in unique_paths(paths) if (
        (p / "Mathlib").is_dir() or (p / "Aesop").is_dir()
        or (p / "Batteries").is_dir() or (p / "Qq").is_dir()
        or (p / "ProofWidgets").is_dir() or (p / "LeanSearchClient").is_dir()
        or (p / "ImportGraph").is_dir() or (p / "Plausible").is_dir()
        or (p / "Cli").is_dir() or any(p.glob("*.olean"))
    )]


def toolchain_evidence(base: Path, version: str) -> Path | None:
    candidates = [
        base / "lean-toolchain",
        base / "_evidence" / "lean-version.log",
        base / "evidence" / "lean-version.log",
        base / ".lake" / "packages" / "mathlib" / "lean-toolchain",
    ]
    for folder in (base / "_evidence", base / "evidence"):
        if folder.is_dir():
            candidates.extend(list(folder.glob("*/lean-version.log"))[:100])
            candidates.extend(list(folder.glob("*/*/lean-version.log"))[:100])
    for path in candidates:
        if not path.is_file():
            continue
        text = read_text(path)
        if path.name == "lean-toolchain":
            if re.fullmatch(r"\s*(?:leanprover/lean4:)?v?" + re.escape(version) + r"\s*", text):
                return path
        elif re.search(r"Lean \(version " + re.escape(version) + r"(?:,|\))", text):
            return path
    return None


def custom_cache_candidates(bases: list[Path], version: str) -> list[tuple[Path, Path, Path]]:
    result: list[tuple[Path, Path, Path]] = []
    for base in bases:
        proof = toolchain_evidence(base, version)
        if not proof:
            continue
        source_roots = [base, base / "backend"]
        for build in (base / "_build" / "lib" / "lean", base / ".lake" / "build" / "lib" / "lean"):
            if build.is_dir():
                for source in source_roots:
                    if source.is_dir():
                        result.append((source, build, proof))
    return result


def audit_output(text: str, expected: list[str]) -> dict[str, list[str]]:
    if BAD_PROOF_RE.search(text):
        raise RunnerError("AUDIT_UNAPPROVED_SORRY")
    found: dict[str, list[str]] = {}
    for match in AUDIT_RE.finditer(text):
        name = match.group(1)
        axioms = [] if match.group(2) is None else [
            token.strip() for token in match.group(2).split(",") if token.strip()
        ]
        if set(axioms) - ALLOWED_AXIOMS:
            raise RunnerError(f"AXIOM_AUDIT_REJECTED|{name}|{axioms}")
        found[name] = axioms
    missing = sorted(set(expected) - set(found))
    if missing:
        raise RunnerError("AXIOM_AUDIT_MISSING|" + ",".join(missing))
    return {name: found[name] for name in expected}


class Builder:
    def __init__(self, root: Path, cfg: dict[str, Any], modules: dict[str, Module],
                 external: list[str], evidence: Path, lean: Path, version_text: str):
        self.root, self.cfg, self.modules = root, cfg, modules
        self.evidence, self.lean, self.version_text = evidence, lean, version_text
        self.build = root / "_build" / "lib" / "lean"
        self.build.mkdir(parents=True, exist_ok=True)
        self.receipt_path = root / "_build" / "cache-v1.json"
        try:
            self.receipts = json.loads(read_text(self.receipt_path))
        except (OSError, ValueError):
            self.receipts = {"format": 1, "modules": {}}
        if self.receipts.get("format") != 1:
            self.receipts = {"format": 1, "modules": {}}
        self.bases = cache_bases(root)
        self.external_roots = cache_library_paths(self.bases)
        self.core_root = lean.parent.parent / "lib" / "lean"
        self.external_roots = unique_paths(self.external_roots + [self.core_root])
        if not any((p / "Mathlib").is_dir() for p in self.external_roots):
            raise RunnerError("CACHED_MATHLIB_NOT_FOUND|set MATHLIB_CACHE_ROOT")
        self.external_files: dict[str, Path] = {}
        self.external_hashes: dict[str, str] = {}
        for name in external:
            relative = module_relative(name, ".olean")
            matches = [p / relative for p in self.external_roots if (p / relative).is_file()]
            if not matches:
                raise RunnerError(f"EXTERNAL_OLEAN_MISSING|{name}|set MATHLIB_CACHE_ROOT")
            self.external_files[name] = matches[0]
            self.external_hashes[name] = sha256(matches[0])
        self.custom_candidates = custom_cache_candidates(self.bases, cfg["toolchain"])
        self.fingerprints: dict[str, str] = {}
        for name, module in modules.items():
            dep_keys = [
                (dep, self.fingerprints[dep] if dep in modules else self.external_hashes[dep])
                for dep in module.imports
            ]
            self.fingerprints[name] = stable_hash({
                "source": module.source_hash, "lean": version_text, "dependencies": dep_keys
            })
        self.env = os.environ.copy()
        # Do not inherit arbitrary session LEAN_PATH entries.
        self.env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [self.build] + self.external_roots)
        self.timeout = int(os.environ.get("RH_LEAN_TIMEOUT_SECONDS", cfg.get("module_timeout_seconds", 1800)))
        self.jobs = max(1, min(8, int(os.environ.get("RH_LEAN_JOBS", cfg.get("jobs", 2)))))
        self.threads = max(1, int(os.environ.get("RH_LEAN_THREADS", cfg.get("lean_threads", 2))))
        self.reuse_events: list[dict[str, Any]] = []
        self.audit_modules = {a["module"] for a in cfg["audit_modules"]}
        self._legacy_valid: dict[tuple[str, str], bool] = {}
        self.process_lock = threading.Lock()
        self.processes: dict[str, subprocess.Popen] = {}
        # Exit code 1 can mean TerminateProcess on Windows, not a Lean error.
        # Protect both the process registry and cancellation provenance together.
        self.cancelled_after_failure: dict[str, str] = {}
        self.abort_after_failure: str | None = None
        atomic_json(evidence / "external-cache-provenance.json", {
            name: {"path": str(path), "sha256": self.external_hashes[name]}
            for name, path in self.external_files.items()
        })

    def output_path(self, name: str) -> Path:
        return self.build / module_relative(name, ".olean")

    def can_reuse_receipt(self, module: Module) -> bool:
        if not module.backend or module.name in self.audit_modules:
            return False
        old = self.receipts.get("modules", {}).get(module.name, {})
        path = self.output_path(module.name)
        if old.get("fingerprint") != self.fingerprints[module.name] or not path.is_file():
            return False
        return old.get("olean_sha256") == sha256(path)

    def legacy_matches(self, name: str, source: Path, cache: Path) -> bool:
        key = (str(source) + "|" + str(cache), name)
        if key in self._legacy_valid:
            return self._legacy_valid[key]
        module = self.modules[name]
        if not module.backend:
            self._legacy_valid[key] = False
            return False
        old_source = source / module_relative(name, ".lean")
        old_olean = cache / module_relative(name, ".olean")
        ok = old_source.is_file() and old_olean.is_file()
        if ok:
            ok = sha256(old_source) == module.source_hash
        if ok:
            # Validate the entire bundled custom dependency closure.
            ok = all(self.legacy_matches(dep, source, cache)
                     for dep in module.imports if dep in self.modules)
        self._legacy_valid[key] = ok
        return ok

    def try_reuse(self, module: Module) -> bool:
        if self.can_reuse_receipt(module):
            emit("CACHED_MODULE_REUSE", module.name)
            return True
        if not module.backend or module.name in self.audit_modules:
            return False
        for source, cache, version_evidence in self.custom_candidates:
            if not self.legacy_matches(module.name, source, cache):
                continue
            old = cache / module_relative(module.name, ".olean")
            dest = self.output_path(module.name)
            dest.parent.mkdir(parents=True, exist_ok=True)
            # Newer Lean versions may emit private/server sidecars.
            for suffix in (".olean", ".olean.private", ".olean.server", ".ilean", ".ir"):
                previous = old.with_name(old.stem + suffix)
                target = dest.with_name(dest.stem + suffix)
                if previous.is_file():
                    shutil.copy2(previous, target)
            event = {
                "module": module.name,
                "source": str(source / module_relative(module.name, ".lean")),
                "source_sha256": module.source_hash,
                "olean": str(old),
                "olean_sha256": sha256(old),
                "toolchain_evidence": str(version_evidence),
                "toolchain_evidence_sha256": sha256(version_evidence),
                "all_custom_dependency_sources_matched": True,
            }
            self.reuse_events.append(event)
            self.record(module)
            emit("SOURCE_MATCHED_CACHE_REUSE", module.name)
            return True
        return False

    def record(self, module: Module) -> None:
        path = self.output_path(module.name)
        self.receipts.setdefault("modules", {})[module.name] = {
            "fingerprint": self.fingerprints[module.name],
            "source_sha256": module.source_hash,
            "lean_version": self.version_text,
            "olean_sha256": sha256(path),
        }

    def _cancel_process_locked(self, name: str, proc: subprocess.Popen, cause: str) -> None:
        # The caller holds process_lock. Preserve independently completed errors.
        if proc.poll() is not None:
            return
        try:
            proc.terminate()
        except OSError as exc:
            # A process can exit between poll and terminate; do not relabel it.
            if proc.poll() is None:
                emit("COMPILE_CANCELLATION_FAILED", f"{name}|CAUSE={cause}|ERROR={exc}")
            return
        self.cancelled_after_failure[name] = cause

    def cancel_after_failure(self, cause: str) -> None:
        with self.process_lock:
            self.abort_after_failure = cause
            for name, proc in self.processes.items():
                self._cancel_process_locked(name, proc, cause)

    def compile_one(self, module: Module) -> tuple[str, int, str, Path]:
        output = self.output_path(module.name)
        output.parent.mkdir(parents=True, exist_ok=True)
        log = self.evidence / "compile" / (module.name + ".log")
        log.parent.mkdir(parents=True, exist_ok=True)
        # Remove stale output before launching; a failed compile cannot reuse it.
        for suffix in (".olean", ".olean.private", ".olean.server", ".ilean", ".ir"):
            stale = output.with_name(output.stem + suffix)
            if stale.is_file():
                stale.unlink()
        cmd = [
            str(self.lean), "--root=" + str(module.source_root),
            "-j", str(self.threads), "-o", str(output), str(module.source)
        ]
        emit("COMPILE", module.name)
        proc = subprocess.Popen(
                cmd, cwd=str(module.source_root), env=self.env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, encoding="utf-8", errors="replace", shell=False,
            )
        with self.process_lock:
            self.processes[module.name] = proc
            # Cover a submitted worker whose Popen was not registered when the
            # scheduler observed the first failure.
            if self.abort_after_failure is not None:
                self._cancel_process_locked(module.name, proc, self.abort_after_failure)
        try:
            stdout, stderr = proc.communicate(timeout=self.timeout)
            content = stdout + stderr
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            proc.kill()
            stdout, stderr = proc.communicate()
            content = stdout + stderr + "\nRUNNER_TIMEOUT=INCONCLUSIVE\n"
            rc = 124
        finally:
            with self.process_lock:
                self.processes.pop(module.name, None)
                cancelled_by = self.cancelled_after_failure.get(module.name)
        if cancelled_by is not None:
            content = (f"RUNNER_CANCELLED_AFTER_FAILURE={cancelled_by}|EXIT={rc}\n"
                       + content)
        log.write_text(content, encoding="utf-8")
        if cancelled_by is None and rc == 0 and (not output.is_file() or BAD_PROOF_RE.search(content)):
            rc = 125
            with log.open("a", encoding="utf-8") as stream:
                stream.write("\nRUNNER_REJECTED=MISSING_OLEAN_OR_SORRY\n")
        return module.name, rc, content, log

    def run(self) -> None:
        pending = set(self.modules)
        done: set[str] = set()
        active: dict[concurrent.futures.Future, tuple[str, float]] = {}
        failed: tuple[str, int, str, Path] | None = None
        last_heartbeat = time.monotonic()
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.jobs) as pool:
            while pending or active:
                if failed is None:
                    ready = sorted(
                        name for name in pending
                        if all(dep not in self.modules or dep in done for dep in self.modules[name].imports)
                    )
                    for name in ready:
                        if len(active) >= self.jobs:
                            break
                        module = self.modules[name]
                        pending.remove(name)
                        if self.try_reuse(module):
                            done.add(name)
                            continue
                        future = pool.submit(self.compile_one, module)
                        active[future] = (name, time.monotonic())
                if not active:
                    if failed:
                        break
                    if pending:
                        # Ready cached nodes may have unlocked more nodes.
                        if any(all(d not in self.modules or d in done for d in self.modules[n].imports)
                               for n in pending):
                            continue
                        raise RunnerError("DEPENDENCY_SCHEDULER_BLOCKED")
                    break
                finished, _ = concurrent.futures.wait(
                    active, timeout=1, return_when=concurrent.futures.FIRST_COMPLETED
                )
                for future in finished:
                    name, _ = active.pop(future)
                    result = future.result()
                    _, rc, content, log = result
                    with self.process_lock:
                        cancelled_by = self.cancelled_after_failure.get(name)
                    if cancelled_by is not None:
                        emit("COMPILE_CANCELLED_AFTER_FAILURE",
                             f"{name}|CAUSE={cancelled_by}|EXIT={rc}|LOG={log}")
                    elif rc != 0:
                        emit("COMPILE_FAIL", f"{name}|EXIT={rc}|LOG={log}")
                        print(content, flush=True)
                        if failed is None:
                            failed = result
                            self.cancel_after_failure(name)
                    else:
                        self.record(self.modules[name])
                        done.add(name)
                        emit("COMPILE_PASS", name)
                if time.monotonic() - last_heartbeat >= 15:
                    for name, start in active.values():
                        emit("COMPILE_RUNNING", f"{name}|SECONDS={int(time.monotonic() - start)}")
                    last_heartbeat = time.monotonic()
                if failed is not None and not active:
                    break
        atomic_json(self.receipt_path, self.receipts)
        atomic_json(self.evidence / "custom-cache-provenance.json", self.reuse_events)
        if failed:
            raise RunnerError(f"DEPENDENCY_BUILD_FAILED|{failed[0]}|{failed[1]}")
        emit("DAG_COMPILE", "PASS")
        self.run_audits()
        self.run_negative_controls()
        if self.cfg.get("rh_theorem"):
            self.run_closed_rh_audit()

    def run_audits(self) -> None:
        combined: dict[str, list[str]] = {}
        for audit in self.cfg["audit_modules"]:
            log = self.evidence / "compile" / (audit["module"] + ".log")
            if not log.is_file():
                raise RunnerError(f"FRESH_AUDIT_LOG_MISSING|{audit['module']}")
            text = read_text(log)
            result = audit_output(text, audit["theorems"])
            combined.update(result)
            for name, axioms in result.items():
                emit("THEOREM_AXIOM_AUDIT", f"PASS_STANDARD_ONLY|{name}|{','.join(axioms)}")
            for fragment in audit.get("expected_fragments", []):
                if fragment not in text:
                    raise RunnerError(f"AUDIT_SIGNATURE_FRAGMENT_MISSING|{fragment}")
        atomic_json(self.evidence / "axiom-audit.json", combined)
        emit("THEOREM_AXIOM_AUDIT_ALL", "PASS_STANDARD_ONLY")

    def run_negative_controls(self) -> None:
        for index, control in enumerate(self.cfg.get("negative_controls", [])):
            path = safe_relative(self.root, control["file"])
            cmd = [str(self.lean), "--root=" + str(self.root), "-j", str(self.threads), str(path)]
            try:
                proc = subprocess.run(
                    cmd, cwd=str(self.root), env=self.env, capture_output=True, text=True,
                    encoding="utf-8", errors="replace", timeout=self.timeout, shell=False,
                )
            except subprocess.TimeoutExpired as exc:
                raise RunnerError(f"NEGATIVE_CONTROL_TIMEOUT|{path.name}") from exc
            text = proc.stdout + proc.stderr
            (self.evidence / f"negative-{index:02d}.log").write_text(text, encoding="utf-8")
            if proc.returncode == 0:
                raise RunnerError(f"NEGATIVE_CONTROL_UNEXPECTED_SUCCESS|{path.name}")
            for fragment in control["expected_fragments"]:
                if fragment not in text:
                    raise RunnerError(f"NEGATIVE_CONTROL_WRONG_FAILURE|{path.name}|{fragment}")
            emit("NEGATIVE_CONTROL", f"PASS|{path.name}")

    def run_closed_rh_audit(self) -> None:
        name = self.cfg["rh_theorem"]
        audited = {theorem for audit in self.cfg["audit_modules"] for theorem in audit["theorems"]}
        if name not in audited:
            raise RunnerError("RH_THEOREM_NOT_EXPLICITLY_AUDITED")
        imports = list(dict.fromkeys(self.cfg["targets"] +
                                    [a["module"] for a in self.cfg["audit_modules"]]))
        for module in imports:
            module_relative(module, ".lean")
        source = self.evidence / "RHRootTypeAudit.lean"
        wrapper = "RHFrontierNativeReplay.closedRH"
        text = "\n".join("import " + module for module in imports) + "\n\n"
        text += "set_option autoImplicit false\nnamespace RHFrontierNativeReplay\n"
        text += "theorem closedRH : _root_.RiemannHypothesis := " + name + "\n"
        text += "#check closedRH\n#print axioms " + name + "\n"
        text += "#print axioms closedRH\nend RHFrontierNativeReplay\n"
        source.write_text(text, encoding="utf-8")
        output = self.evidence / "RHRootTypeAudit.olean"
        cmd = [str(self.lean), "--root=" + str(self.evidence), "-j", str(self.threads),
               "-o", str(output), str(source)]
        try:
            proc = subprocess.run(cmd, cwd=str(self.evidence), env=self.env,
                                  capture_output=True, text=True, encoding="utf-8",
                                  errors="replace", timeout=self.timeout, shell=False)
        except subprocess.TimeoutExpired as exc:
            raise RunnerError("CLOSED_RH_TYPE_AUDIT_TIMEOUT") from exc
        content = proc.stdout + proc.stderr
        (self.evidence / "closed-rh-type-audit.log").write_text(content, encoding="utf-8")
        if proc.returncode != 0 or not output.is_file():
            print(content, flush=True)
            raise RunnerError("CLOSED_LITERAL_RH_TYPE_CHECK_FAILED")
        result = audit_output(content, [name, wrapper])
        atomic_json(self.evidence / "closed-rh-audit.json", {
            "theorem": name, "closed_wrapper": wrapper, "axioms": result,
            "source_sha256": sha256(source), "olean_sha256": sha256(output),
        })
        emit("CLOSED_LITERAL_RH_TYPE_CHECK", "PASS|" + name)
        emit("CLOSED_RH_AXIOM_AUDIT", "PASS_STANDARD_ONLY|" + wrapper)


def scheduler_cancellation_self_test() -> None:
    """Exercise the real scheduler with fake Popen children; never launch Lean."""
    from contextlib import redirect_stdout
    from io import StringIO
    from unittest.mock import patch

    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        builder = Builder.__new__(Builder)
        builder.build = root / "build"
        builder.evidence = root / "evidence"
        builder.receipt_path = root / "receipts.json"
        builder.receipts = {"format": 1, "modules": {}}
        builder.reuse_events = []
        builder.lean = root / "FAKE_COMPILER_NEVER_EXECUTED"
        builder.threads, builder.jobs, builder.timeout = 1, 3, 5
        builder.env = {}
        builder.cfg = {}
        builder.process_lock = threading.Lock()
        builder.processes = {}
        builder.cancelled_after_failure = {}
        builder.abort_after_failure = None
        names = ("A.RootFailure", "B.CancelledSibling", "C.IndependentFailure")
        builder.modules = {
            name: Module(name, root / (name + ".lean"), root, (), "fixture", False)
            for name in names
        }
        builder.try_reuse = lambda module: False
        recorded = []
        builder.record = lambda module: recorded.append(module.name)
        all_started = threading.Event()
        sibling_terminated = threading.Event()
        children = {}
        children_lock = threading.Lock()

        class FakeProcess:
            def __init__(self, cmd, **kwargs):
                self.name = Path(cmd[-1]).stem
                self.returncode = 1 if self.name == names[2] else None
                self.terminated = False
                with children_lock:
                    children[self.name] = self
                    if all(name in children for name in names):
                        all_started.set()

            def poll(self):
                return self.returncode

            def terminate(self):
                assert self.returncode is None, "completed child must not be cancelled"
                self.terminated = True
                # Reproduce native Windows TerminateProcess's error-like exit.
                self.returncode = 1
                sibling_terminated.set()

            def communicate(self, timeout=None):
                if self.name == names[0]:
                    assert all_started.wait(5), "fixture children failed to start"
                    self.returncode = 1
                    return "ROOT_PROOF_ERROR\n", ""
                assert sibling_terminated.wait(5), "running child was not cancelled"
                if self.name == names[2]:
                    return "INDEPENDENT_PROOF_ERROR\n", ""
                return "", ""

        transcript = StringIO()
        with patch.object(subprocess, "Popen", FakeProcess), redirect_stdout(transcript):
            try:
                builder.run()
            except RunnerError as exc:
                assert str(exc) == "DEPENDENCY_BUILD_FAILED|A.RootFailure|1"
            else:
                raise AssertionError("scheduler accepted a failed dependency")
            # Also cover a submitted task registering after failure was observed.
            late = Module("D.LateRegistration", root / "D.LateRegistration.lean",
                          root, (), "fixture", False)
            _, late_rc, late_content, _ = builder.compile_one(late)
        output = transcript.getvalue()
        assert "COMPILE_FAIL=A.RootFailure|" in output
        assert "COMPILE_FAIL=C.IndependentFailure|" in output
        assert "INDEPENDENT_PROOF_ERROR" in output
        assert "COMPILE_CANCELLED_AFTER_FAILURE=B.CancelledSibling|CAUSE=A.RootFailure|" in output
        assert "COMPILE_FAIL=B.CancelledSibling|" not in output
        assert "COMPILE_PASS=" not in output and not recorded
        assert children[names[1]].terminated
        assert not children[names[2]].terminated
        cancelled_log = read_text(builder.evidence / "compile" / (names[1] + ".log"))
        assert cancelled_log.startswith("RUNNER_CANCELLED_AFTER_FAILURE=A.RootFailure|EXIT=1\n")
        assert "INDEPENDENT_PROOF_ERROR" in read_text(
            builder.evidence / "compile" / (names[2] + ".log"))
        assert late_rc == 1 and children[late.name].terminated
        assert late_content.startswith("RUNNER_CANCELLED_AFTER_FAILURE=A.RootFailure|EXIT=1\n")
        assert builder.cancelled_after_failure == {
            names[1]: names[0], late.name: names[0]
        }
    emit("SCHEDULER_CANCELLATION_SELF_TEST", "PASS_FAKE_CHILDREN_ONLY")


def self_test() -> None:
    assert "Hidden" not in strip_comments("/- import Hidden /- nested -/ -/\nimport Good\n")
    assert audit_output("'A.b' depends on axioms: [propext,\n Classical.choice]\n", ["A.b"]) == {
        "A.b": ["propext", "Classical.choice"]
    }
    assert audit_output("'A.c' does not depend on any axioms\n", ["A.c"]) == {"A.c": []}
    for text, expected in [
        ("'A.b' depends on axioms: [sorryAx]", ["A.b"]),
        ("'A.b' depends on axioms: [Extra.axiom]", ["A.b"]),
        ("", ["A.b"]),
    ]:
        try:
            audit_output(text, expected)
        except RunnerError:
            pass
        else:
            raise AssertionError("audit rejection failed")
    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        (root / "Root.lean").write_text(
            "/- import Hidden /- import AlsoHidden -/ -/\n"
            "import Dep\n-- import Wrong\n"
            'def text : String := "import NotAModule"\n',
            encoding="utf-8",
        )
        (root / "Dep.lean").write_text("import Mathlib.Data.Nat.Basic\n", encoding="utf-8")
        assert imports_of(root / "Root.lean") == ["Dep"]
        cfg = {"targets": ["Root"], "audit_modules": [], "source_roots": ["."]}
        modules, external = build_graph(root, cfg)
        assert list(modules) == ["Dep", "Root"]
        assert external == ["Mathlib.Data.Nat.Basic"]
        (root / "Dep.lean").write_text("import Root\n", encoding="utf-8")
        try:
            build_graph(root, cfg)
        except RunnerError as exc:
            assert "IMPORT_CYCLE" in str(exc)
        else:
            raise AssertionError("cycle not rejected")
        manifest = {"files": {"Root.lean": sha256(root / "Root.lean"),
                              "Dep.lean": sha256(root / "Dep.lean")}}
        atomic_json(root / "source-manifest.json", manifest)
        verify_manifest(root)
        (root / "Dep.lean").write_text("tampered", encoding="utf-8")
        try:
            verify_manifest(root)
        except RunnerError as exc:
            assert "SOURCE_MANIFEST_MISMATCH" in str(exc)
        else:
            raise AssertionError("manifest tampering accepted")
    scheduler_cancellation_self_test()
    emit("RUNNER_SELF_TEST", "PASS")
    emit("LEAN_EXECUTION", "NONE")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-config", action="store_true",
                        help="Validate package/config/graph without launching Lean")
    parser.add_argument("--self-test", action="store_true",
                        help="Run Python-only parser/audit/manifest/scheduler tests")
    parser.add_argument("--config", type=Path,
                        help="Use a manifest-covered generated admission configuration")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    root = PACKAGE_ROOT
    config_path = args.config.resolve() if args.config else root / "scripts" / "build_config.json"
    cfg = load_config(root, config_path)
    manifest = verify_manifest(root)
    covered = {safe_relative(root, name) for name in manifest}
    if cfg.get("extra_manifest"):
        extra_manifest = Path(cfg["extra_manifest"])
        if not extra_manifest.is_absolute():
            extra_manifest = (config_path.parent / extra_manifest).resolve()
        extra_root = extra_manifest.parent
        extras = verify_manifest(extra_root, extra_manifest)
        covered.update(safe_relative(extra_root, name) for name in extras)
    if config_path.resolve() not in covered:
        raise RunnerError("BUILD_CONFIG_NOT_COVERED_BY_MANIFEST")
    modules, external = build_graph(root, cfg)
    for module in modules.values():
        if module.source.resolve() not in covered:
            raise RunnerError(f"COMPILED_SOURCE_NOT_COVERED_BY_MANIFEST|{module.name}")
    for control in cfg.get("negative_controls", []):
        if safe_relative(root, control["file"]) not in covered:
            raise RunnerError(f"NEGATIVE_SOURCE_NOT_COVERED_BY_MANIFEST|{control['file']}")
    emit("SOURCE_MANIFEST", "PASS")
    emit("PACKAGE", cfg["package"])
    emit("PACKAGE_ROOT", root)
    emit("DAG_LOCAL_MODULES", len(modules))
    emit("DAG_EXTERNAL_MODULES", len(external))
    if args.check_config:
        emit("STATIC_CONFIG", "PASS")
        emit("LEAN_EXECUTION", "NONE")
        return 0
    if os.name != "nt":
        raise RunnerError("NATIVE_WINDOWS_REQUIRED|use --check-config for static validation")
    home = Path(os.environ.get("USERPROFILE", str(Path.home())))
    lean = Path(os.environ.get(
        "LEAN_EXE",
        str(home / ".elan" / "toolchains" / "leanprover--lean4---v4.33.0" / "bin" / "lean.exe"),
    ))
    if not lean.is_file():
        raise RunnerError(f"LEAN_433_NOT_FOUND|{lean}")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"-{os.getpid()}"
    evidence = root / "_evidence" / stamp
    evidence.mkdir(parents=True, exist_ok=False)
    version = subprocess.run(
        [str(lean), "--version"], capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=30, shell=False,
    )
    version_text = (version.stdout + version.stderr).strip()
    (evidence / "lean-version.log").write_text(version_text + "\n", encoding="utf-8")
    if version.returncode != 0 or not re.search(
        r"Lean \(version " + re.escape(cfg["toolchain"]) + r"(?:,|\))", version_text
    ):
        raise RunnerError(f"LEAN_VERSION_MISMATCH|{version_text}")
    emit("LEAN_VERSION", version_text)
    emit("EVIDENCE", evidence)
    emit("MODE", "NATIVE_WINDOWS_CACHED_DEPENDENCIES")
    emit("NETWORK", "NOT_USED")
    emit("LAKE", "NOT_USED")
    emit("POWERSHELL", "NOT_USED")
    builder = Builder(root, cfg, modules, external, evidence, lean, version_text)
    try:
        builder.run()
    except Exception as exc:
        atomic_json(evidence / "result.json", {
            "status": "FAIL_OR_INCONCLUSIVE", "error": str(exc),
            "package": cfg["package"], "lean_version": version_text,
        })
        raise
    result = {
        "status": "PASS", "package": cfg["package"], "lean_version": version_text,
        "scope": cfg.get("scope", "PROOF_CARRYING_FINITE_ADMISSION"),
        "raw_theta_source_checker": "NOT_ESTABLISHED",
        "universal_numerical_tail_checker": "OPEN",
        "rh_witness_exhibited": bool(cfg.get("rh_theorem")),
    }
    atomic_json(evidence / "result.json", result)
    emit("SOURCE_SCOPE", result["scope"])
    emit("RAW_THETA_SOURCE_CHECKER", "NOT_ESTABLISHED")
    emit("UNIVERSAL_NUMERICAL_TAIL_CHECKER", "OPEN")
    emit("RH_WITNESS_EXHIBITED", "TRUE" if result["rh_witness_exhibited"] else "FALSE")
    emit("PROMOTION", "MATCHING_EXTERNAL_EVIDENCE_REQUIRED")
    emit("RUN", "PASS_NATIVE_RH_ADMISSION" if result["rh_witness_exhibited"]
         else cfg.get("pass_status", "PASS_FINITE_PROOF_CARRYING_FRONTIER"))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RunnerError, OSError, ValueError, subprocess.SubprocessError) as exc:
        emit("ERROR", str(exc))
        emit("RUN", "FAIL_OR_INCONCLUSIVE")
        raise SystemExit(1)

