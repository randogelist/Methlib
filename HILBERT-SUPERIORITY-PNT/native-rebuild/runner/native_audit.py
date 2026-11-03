#!/usr/bin/env python3
"""External Lean build / named-axiom and dependency-diagnostic runner.

No local Lean is executed by authoring this script. A machine invoking this
script must provide a pinned, pre-existing Mathlib build cache and the native
4.34.0-rc1 Lean executable. Every candidate is built from its supplied source.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(os.environ.get('HVR_REBUILD_ROOT', Path(__file__).resolve().parent.parent)).resolve()
BASE_SHA = 'eaa4d4734e3e08da59715d2370262efb051bb6332a8b73ae84b03249bc68fd4c'
BASE_MANIFEST = '2175cc322b8908365ccc2a1c29d1362fe0c96141ce87d4646214f056b541720f'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
IDENT = re.compile(r'^[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*$', flags=re.UNICODE)


def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def die(message):
    print('RUNNER_ERROR=' + str(message), flush=True)
    return 2


def load_plan():
    path = ROOT / 'plan.json'
    plan = json.loads(path.read_text(encoding='utf-8'))
    if not isinstance(plan, list) or not plan:
        raise ValueError('plan must be a nonempty JSON array')
    modules, names = set(), set()
    for entry in plan:
        if not isinstance(entry, dict) or set(entry) != {'module', 'names', 'banned'}:
            raise ValueError('each plan entry must have exactly module, names, banned')
        module, ds, banned = entry['module'], entry['names'], entry['banned']
        if not isinstance(module, str) or not IDENT.fullmatch(module) or '.' in module or module in modules:
            raise ValueError('invalid or duplicate module ' + str(module))
        modules.add(module)
        for label, seq in [('names', ds), ('banned', banned)]:
            if not isinstance(seq, list) or not seq or any(not isinstance(x, str) or not IDENT.fullmatch(x) or (label == 'names' and '.' not in x) for x in seq):
                raise ValueError('invalid ' + label + ' in ' + module)
        if len(ds) != len(set(ds)) or any(n in names for n in ds):
            raise ValueError('duplicate theorem audit name')
        names.update(ds)
        if not (ROOT / 'candidates' / (module + '.lean')).is_file():
            raise ValueError('missing candidate ' + module)
    # Require a checked-in immutable source manifest, not just a log generated
    # after running. Its own SHA256 is always recorded in the evidence.
    manifest = ROOT / 'sources.sha256'
    supplied = {}
    for line in manifest.read_text(encoding='utf-8').splitlines():
        m = re.fullmatch(r'([0-9a-f]{64})  (plan\.json|candidates/[A-Za-z_][\w]*\.lean)', line)
        if not m or m.group(2) in supplied:
            raise ValueError('invalid or duplicate source manifest entry: ' + line[:100])
        supplied[m.group(2)] = m.group(1)
    expected = {'plan.json'} | {'candidates/' + e['module'] + '.lean' for e in plan}
    if set(supplied) != expected:
        raise ValueError('manifest does not enumerate exactly plan and candidates')
    for name, expected_digest in supplied.items():
        if sha256(ROOT / name) != expected_digest:
            raise ValueError('source hash mismatch: ' + name)
    return plan


def restore_old_project_objects(path, out, compiler, witness):
    """Optional exact Linux CI artifact reuse; check zip, provenance and objects.

    This validates selected provenance fields only; full Mathlib object
    provenance was not recorded and must not be claimed. The bundle is never
    cross-platform: it is the earlier Linux 4.34-rc1 artifact.
    """
    if not path.is_file():
        print('PROJECT_BASE_CACHE=NOT_SUPPLIED', flush=True)
        return None
    if sha256(path) != BASE_SHA:
        raise ValueError('previous Linux evidence artifact checksum differs')
    with zipfile.ZipFile(path) as z:
        names = z.namelist()
        def exactly_one(suffix):
            matches = [n for n in names if n.endswith('/' + suffix)]
            if len(matches) != 1: raise ValueError('missing or ambiguous baseline ' + suffix)
            return matches[0]
        result = z.read(exactly_one('result.txt')).decode('utf-8')
        version = z.read(exactly_one('lean-version.txt')).decode('utf-8')
        prov = json.loads(z.read(exactly_one('provenance.json')))
        if 'RESULT=PASS\n' not in result or 'COMBINED_BUILD_AND_NAMED_AXIOM_AUDIT=PASS\n' not in result:
            raise ValueError('baseline combined build did not pass')
        if not version.startswith('Lean (version 4.34.0-rc1,'):
            raise ValueError('baseline Lean version mismatch')
        if prov.get('source_manifest_sha256') != BASE_MANIFEST:
            raise ValueError('baseline source manifest mismatch')
        if prov.get('compiler_sha256') != sha256(compiler) or prov.get('mathlib_witness_sha256') != sha256(witness):
            raise ValueError('baseline compiler or Mathlib witness differs')
        modules = prov.get('modules', {})
        for module, entry in modules.items():
            if not IDENT.fullmatch(module) or '.' in module or not entry.get('object_sha256'):
                raise ValueError('invalid baseline module object record')
            member = exactly_one('olean/' + module + '.olean')
            data = z.read(member)
            if hashlib.sha256(data).hexdigest() != entry['object_sha256']:
                raise ValueError('baseline object hash mismatch: ' + module)
            (out / (module + '.olean')).write_bytes(data)
    print('PROJECT_BASE_CACHE=VERIFIED_PRIOR_LINUX_EVIDENCE', flush=True)
    print('BASE_MATHLIB_FULL_CACHE_PROVENANCE=NOT_INDEPENDENTLY_VERIFIED', flush=True)
    return {'artifact_sha256': BASE_SHA, 'source_manifest_sha256': BASE_MANIFEST,
            'objects': len(modules), 'mathlib_provenance': 'one witness verified; full cache not independently verified'}


def main():
    plan = load_plan()
    print('PLAN_AND_HASHES=PASS CANDIDATES=' + str(len(plan)), flush=True)
    if '--check-plan' in sys.argv[1:]:
        return 0
    cache = Path(os.environ['MATHLIB_CACHE_ROOT']).resolve()
    lib = cache / '.lake/build/lib/lean'
    witness = lib / 'Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.olean'
    if not witness.is_file(): raise ValueError('Mathlib cache witness not found')
    lean = Path(os.environ['LEAN_EXE']).resolve()
    version = subprocess.run([lean, '--version'], capture_output=True, text=True, check=True).stdout.strip()
    if not version.startswith('Lean (version 4.34.0-rc1,'):
        raise ValueError('wrong Lean version: ' + version)
    if 'linux' not in version.lower():
        raise ValueError('expected native Linux compiler for Linux evidence reuse')
    tag = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
    ev = ROOT / 'evidence-linux' / tag
    candidates_out = ev / 'candidate-olean'
    project_out = ev / 'project-olean'
    candidates_out.mkdir(parents=True)
    project_out.mkdir()
    print('EVIDENCE=' + str(ev), flush=True)
    baseline = restore_old_project_objects(ROOT / 'verification' / 'linux_rc1_evidence.zip', project_out, lean, witness)
    deps = sorted((cache / '.lake/packages').glob('*/.lake/build/lib/lean'))
    lean_path = [candidates_out, project_out, lib] + [p for p in deps if p.is_dir()]
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, lean_path))
    (ev / 'lean-version.txt').write_text(version + '\n', encoding='utf-8')
    (ev / 'lean-path.txt').write_text('\n'.join(map(str, lean_path)) + '\n', encoding='utf-8')
    records = {'lean_version': version, 'lean_sha256': sha256(lean), 'mathlib_witness_sha256': sha256(witness),
               'sources_manifest_sha256': sha256(ROOT / 'sources.sha256'), 'baseline': baseline,
               'dependency_trace_coverage': 'UNVERIFIED', 'candidates': {}}
    (ev / 'plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    shutil.copy2(ROOT / 'sources.sha256', ev / 'sources.sha256')
    failed = False
    proof_failed = False
    dependency_found = []
    nonblocking = '--allow-known-dependencies' in sys.argv[1:]
    expected_findings = {}
    if nonblocking:
        known_path = ROOT / 'known-dependencies.json'
        known = json.loads(known_path.read_text(encoding='utf-8'))
        expected_findings = known['theorems']
        if not isinstance(expected_findings, dict) or not expected_findings:
            raise ValueError('known dependency baseline is missing or empty')
        for theorem, item in expected_findings.items():
            match = next((e for e in plan if e['module'] == item['module'] and theorem in e['names']), None)
            if not match or sha256(ROOT / 'candidates' / (item['module'] + '.lean')) != item['source_sha256']:
                raise ValueError('known dependency baseline source or theorem mismatch: ' + theorem)
            if not isinstance(item['targets'], list) or not set(item['targets']).issubset(match['banned']):
                raise ValueError('known dependency targets invalid for ' + theorem)
        records['known_dependency_manifest_sha256'] = sha256(known_path)
        records['known_dependency_evidence_run'] = known['evidence_run']
    print('DEPENDENCY_POLICY=' + ('KNOWN_BASELINE_NONBLOCKING' if nonblocking else 'STRICT'), flush=True)
    for entry in plan:
        module = entry['module']
        rec = records['candidates'][module] = {'source_sha256': sha256(ROOT / 'candidates' / (module + '.lean'))}
        print('SOURCE_SHA256=' + module + ' ' + rec['source_sha256'], flush=True)
        for name in entry['names']:
            print('THEOREM_ALIAS=' + module + ' ' + name, flush=True)
        for target in entry['banned']:
            print('TARGET_ALIAS=' + module + ' ' + target, flush=True)
        def run(label, args):
            print('STAGE_START=' + label, flush=True)
            with (ev / (label + '.stdout.log')).open('wb') as stdout, (ev / (label + '.stderr.log')).open('wb') as stderr:
                p = subprocess.run([str(lean), *map(str, args)], cwd=ROOT / 'candidates', env=env, stdout=stdout, stderr=stderr)
            ok = p.returncode == 0
            print('STAGE_' + ('PASS=' if ok else 'FAIL=') + label, flush=True)
            if not ok:
                for suffix in ('.stdout.log', '.stderr.log'):
                    print((ev / (label + suffix)).read_text(encoding='utf-8', errors='replace'), flush=True)
            return ok
        obj = candidates_out / (module + '.olean')
        if not run('build_' + module, ['-o', obj, module + '.lean']) or not obj.is_file():
            rec['build'] = 'FAIL'; failed = True; proof_failed = True; continue
        rec['build'] = 'PASS'; rec['object_sha256'] = sha256(obj)
        audit = ev / ('audit_' + module + '.lean')
        audit.write_text('import ' + module + '\n' + ''.join('#check ' + n + '\n#print axioms ' + n + '\n' for n in entry['names']), encoding='utf-8')
        rec['audit_source_sha256'] = sha256(audit)
        audit_invocation_ok = run('audit_' + module, [audit])
        if not audit_invocation_ok:
            rec['axiom_audit'] = 'FAIL'; failed = True
        log = (ev / ('audit_' + module + '.stdout.log')).read_text(encoding='utf-8', errors='replace')
        all_ok = audit_invocation_ok
        for name in entry['names']:
            pattern = (r"'" + re.escape(name) + r"' (?:depends on axioms: \[(?P<axs>[^\]]*)\]|(?P<none>does not depend on any axioms))")
            report = re.search(pattern, log, flags=re.DOTALL)
            if not report:
                print('MISSING_AXIOM_REPORT=' + name, flush=True); all_ok = False; continue
            if report.group('none') is None:
                for axiom in (s.strip() for s in report.group('axs').split(',')):
                    if axiom and axiom not in ALLOWED:
                        print('UNAPPROVED_AXIOM=' + name + ' ' + axiom, flush=True); all_ok = False
        rec['axiom_audit'] = 'STANDARD_ONLY' if all_ok else 'FAIL'
        if not all_ok: failed = True; proof_failed = True
        # A target found in Lean's transitive traversal is conclusive evidence
        # of dependence. A missing target is NOT an independence certificate:
        # imported theorem bodies may be opaque/unavailable to this diagnostic.
        rec['dependency_diagnostics'] = {}
        for idx, name in enumerate(entry['names']):
            trace = ev / ('trace_' + module + '_' + str(idx) + '.lean')
            banned = ', '.join('`' + n for n in entry['banned'])
            trace.write_text('import ' + module + '\nimport ImportGraph.Imports.RequiredModules\n'
                'open Lean Elab Command\nset_option maxHeartbeats 0 in\nrun_cmd do\n'
                '  let root : Name := `' + name + '\n'
                '  let banned : Array Name := #[' + banned + ']\n'
                '  let deps ← liftCoreM root.transitivelyUsedConstants\n'
                '  let env ← getEnv\n'
                '  for target in banned do\n'
                '    if (env.find? target).isNone then\n'
                '      IO.println s!"TARGET_UNKNOWN={target}"\n'
                '    else if root == target || deps.contains target then\n'
                '      IO.println s!"TARGET_FOUND={target}"\n'
                '    else\n'
                '      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={target}"\n', encoding='utf-8')
            label = 'trace_' + module + '_' + str(idx)
            if not run(label, [trace]):
                rec['dependency_diagnostics'][name] = 'TRACE_UNAVAILABLE_COVERAGE_UNVERIFIED'
                if nonblocking: failed = True
                continue
            log = (ev / (label + '.stdout.log')).read_text(encoding='utf-8', errors='replace')
            expected = set(entry['banned'])
            for line in log.splitlines():
                if line.startswith(('TARGET_FOUND=', 'TARGET_UNKNOWN=', 'TARGET_NOT_SEEN_COVERAGE_UNVERIFIED=')):
                    print('DEPENDENCY_DIAGNOSTIC=' + name + ' ' + line, flush=True)
            found = {line.split('=', 1)[1].strip() for line in log.splitlines() if line.startswith('TARGET_FOUND=')}
            absent = {line.split('=', 1)[1].strip() for line in log.splitlines() if line.startswith('TARGET_NOT_SEEN_COVERAGE_UNVERIFIED=')}
            if nonblocking and name == 'HVRNextEulerPrimeZetaBridge.eulerProductLogDerivative' and len(found | absent) != len(expected):
                print('ROOT_DEPENDENCY_TRACE_INCOMPLETE', flush=True)
                failed = True
            if found:
                rec['dependency_diagnostics'][name] = {'status': 'TARGET_FOUND', 'targets': sorted(found)}
                print('FORBIDDEN_DEPENDENCY_FOUND=' + name + ' TARGETS=' + ','.join(sorted(found)), flush=True)
                allowed = set(expected_findings.get(name, {}).get('targets', [])) if nonblocking else set()
                unexpected = found - allowed
                dependency_found.append({'theorem': name, 'targets': sorted(found), 'unexpected': sorted(unexpected)})
                if unexpected:
                    print('UNEXPECTED_DEPENDENCY_FOUND=' + name + ' TARGETS=' + ','.join(sorted(unexpected)), flush=True)
                if not nonblocking or unexpected: failed = True
            elif absent == expected:
                rec['dependency_diagnostics'][name] = 'TARGET_NOT_SEEN_COVERAGE_UNVERIFIED'
            else:
                rec['dependency_diagnostics'][name] = 'TRACE_INCOMPLETE_COVERAGE_UNVERIFIED'
    dependency_status = 'TARGETS_FOUND' if dependency_found else 'NO_TARGET_FOUND_COVERAGE_UNVERIFIED'
    records['dependency_gate'] = dependency_status
    records['dependency_policy'] = 'KNOWN_BASELINE_NONBLOCKING' if nonblocking else 'STRICT'
    records['dependency_findings'] = dependency_found
    (ev / 'provenance.json').write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    result = ('FAIL' if failed else ('PASS_BUILD_AND_AXIOM_AUDIT_ONLY' if nonblocking else 'PASS'))
    proof_result = 'FAIL' if proof_failed else 'PASS'
    result_text = ('RESULT=' + result + '\n'
        + 'BUILD_AND_NAMED_AXIOM_AUDIT=' + proof_result + '\n'
        + 'DEPENDENCY_GATE=' + dependency_status + '\n'
        + 'DEPENDENCY_POLICY=' + ('KNOWN_BASELINE_NONBLOCKING' if nonblocking else 'STRICT') + '\n'
        + 'DEPENDENCY_TRACE_COVERAGE=UNVERIFIED\n'
        + 'MATHLIB_FULL_CACHE_PROVENANCE=NOT_INDEPENDENTLY_VERIFIED\n')
    (ev / 'result.txt').write_text(result_text, encoding='utf-8')
    print(result_text, end='', flush=True)
    return 1 if failed else 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, subprocess.SubprocessError, zipfile.BadZipFile) as e:
        raise SystemExit(die(e))
