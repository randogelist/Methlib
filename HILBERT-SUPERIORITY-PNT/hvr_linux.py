#!/usr/bin/env python3
"""Run the Windows package's 120-stage plan on Linux.

The plan and expected theorem names are read from run.ps1. Every
project module is rebuilt from source and its named declarations are audited;
only the separately obtained Mathlib/dependency cache is reused.
"""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

PKG = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = 'HVR_PrimeDensity_FinalRoot'
ROOT_NAMES = {'HVRPrimeDensityFinalRoot.backwardDecomposition',
              'HVRPrimeDensityFinalRoot.actual_prime_concentrated_smoothing',
              'HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one'}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def get_plan():
    script = (PKG / 'run.ps1').read_text(encoding='utf-8')
    m = re.search(r'(?ms)^  \$plan = @\(\s*\n(.*?)^  \)', script)
    if not m:
        raise ValueError('original build plan not found')
    entry_re = re.compile(r"^\s*@\{ module = '([^']+)'; deps = @\((.*?)\); names = @\((.*?)\) \},?\s*$")
    quoted = re.compile(r"'([^']+)'")
    entries = []
    for line in m.group(1).splitlines():
        if not line.strip():
            continue
        parsed = entry_re.fullmatch(line)
        if not parsed:
            raise ValueError('unparseable plan entry: ' + line[:160])
        module, deps, names = parsed.groups()
        def items(raw):
            out = quoted.findall(raw)
            if quoted.sub('', raw).strip(' ,'):
                raise ValueError('invalid quoted list')
            return out
        entries.append({'module': module, 'deps': items(deps), 'names': items(names)})
    if len(entries) != 120:
        raise ValueError(f'expected 120 modules; found {len(entries)}')
    seen = set()
    for entry in entries:
        mod = entry['module']
        if mod in seen or any(d not in seen for d in entry['deps']) or not entry['names']:
            raise ValueError(f'duplicate, unordered dependency, or empty audit: {mod}')
        for f in (PKG / (mod + '.lean'), PKG / ('Audit_' + mod + '.lean')):
            if not f.is_file():
                raise ValueError(f'missing file {f.name}')
        seen.add(mod)
    if entries[-1]['module'] != ROOT or set(entries[-1]['names']) != ROOT_NAMES:
        raise ValueError('final root or its named audits do not match')
    return entries


def run():
    plan = get_plan()
    if '--check-plan' in sys.argv[1:]:
        print(f'PLAN_CHECK=PASS MODULES={len(plan)} NAMED_REPORTS={sum(len(e["names"]) for e in plan)}')
        return 0
    cache = Path(os.environ.get('MATHLIB_CACHE_ROOT', '')).resolve()
    if not os.environ.get('MATHLIB_CACHE_ROOT'):
        raise ValueError('MATHLIB_CACHE_ROOT must name the cached Mathlib checkout')
    ml = cache / '.lake/build/lib/lean'
    witness = ml / 'Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.olean'
    if not witness.is_file():
        raise ValueError(f'Mathlib cache witness not found: {witness}')
    lean = os.environ.get('LEAN_EXE') or shutil.which('lean')
    if not lean:
        raise ValueError('Lean executable not found')
    version = subprocess.run([lean, '--version'], text=True, capture_output=True, check=True).stdout.strip()
    if not re.match(r'^Lean \(version 4\.34\.0-rc1,', version):
        raise ValueError(f'unexpected compiler version: {version}')
    prefix = subprocess.run([lean, '--print-prefix'], text=True, capture_output=True, check=True).stdout.strip()
    compiler = Path(prefix) / 'bin/lean'
    if not compiler.is_file():
        raise ValueError('real Lean executable unavailable under --print-prefix')
    tag = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
    ev = PKG / 'evidence-linux' / tag
    objects = ev / 'olean'
    objects.mkdir(parents=True)
    print(f'EVIDENCE={ev}', flush=True)
    dependencies = sorted((cache / '.lake/packages').glob('*/.lake/build/lib/lean'))
    paths = [objects, ml] + [p for p in dependencies if p.is_dir()]
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
    (ev / 'lean-path.txt').write_text('\n'.join(str(p) for p in paths) + '\n')
    (ev / 'lean-version.txt').write_text(version + '\n')
    records = {'compiler_sha256': digest(compiler), 'mathlib_witness_sha256': digest(witness),
               'compiler': str(compiler), 'mathlib_root': str(cache),
               'cache_provenance': 'externally obtained; full cache not independently hashed',
               'plan_source_sha256': digest(PKG / 'run.ps1'), 'modules': {}}
    (ev / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    states = {}
    ok_all = True

    def invoke(args, name):
        print(f'STAGE_START={name}', flush=True)
        with (ev / (name + '.stdout.log')).open('wb') as out, (ev / (name + '.stderr.log')).open('wb') as err:
            result = subprocess.run([str(compiler), *map(str, args)], cwd=PKG, env=env,
                                    stdout=out, stderr=err)
        print(f'STAGE_{"PASS" if result.returncode == 0 else "FAIL"}={name}', flush=True)
        if result.returncode:
            for suffix in ('stdout.log', 'stderr.log'):
                print((ev / (name + '.' + suffix)).read_text(encoding='utf-8', errors='replace'), flush=True)
        return result.returncode == 0

    for item in plan:
        module = item['module']
        src = PKG / (module + '.lean')
        obj = objects / (module + '.olean')
        record = records['modules'][module] = {'source_sha256': digest(src),
                                               'audit_sha256': digest(PKG / ('Audit_' + module + '.lean'))}
        missing = [dep for dep in item['deps'] if states.get(dep) != 'PASS']
        if missing:
            print(f'BLOCKED={module} DEPENDENCIES={",".join(missing)}', flush=True)
            states[module] = 'BLOCKED'
            ok_all = False
            continue
        print(f'CACHE_MISS={module} BUILD_FROM_SOURCE', flush=True)
        if not invoke(['-o', obj, module + '.lean'], 'build_' + module) or not obj.is_file():
            states[module] = 'FAIL'
            ok_all = False
            continue
        record['object_sha256'] = digest(obj)
        states[module] = 'PASS'

    for item in plan:
        module = item['module']
        if states[module] != 'PASS':
            print(f'AUDIT_SKIPPED={module} BUILD={states[module]}', flush=True)
            continue
        audit = PKG / ('Audit_' + module + '.lean')
        name = 'audit_' + module
        if not invoke([audit], name):
            ok_all = False
            print(f'AXIOM_AUDIT_FAIL={module}', flush=True)
            continue
        log = (ev / (name + '.stdout.log')).read_text(encoding='utf-8', errors='replace')
        audit_ok = True
        for declaration in item['names']:
            pattern = (r"'" + re.escape(declaration) + r"' (?:depends on axioms: \[(?P<axs>[^\]]*)\]|(?P<none>does not depend on any axioms))")
            match = re.search(pattern, log, flags=re.DOTALL)
            if not match:
                print(f'MISSING_AXIOM_REPORT={declaration}', flush=True)
                audit_ok = False
                continue
            if match.group('none') is None:
                for axiom in (x.strip() for x in match.group('axs').split(',')):
                    if axiom and axiom not in ALLOWED:
                        print(f'UNAPPROVED_AXIOM={declaration} AXIOM={axiom}', flush=True)
                        audit_ok = False
        print(f'AXIOM_AUDIT_{"STANDARD_ONLY" if audit_ok else "FAIL"}={module}', flush=True)
        if not audit_ok:
            ok_all = False
    (ev / 'provenance.json').write_text(json.dumps(records, indent=2) + '\n')
    (ev / 'result.txt').write_text(('RESULT=PASS\nSCOPE=THETA_RATIO_ROOT\nTHETA_ROOT_BUILD_AND_NAMED_AXIOM_AUDIT=PASS\n' if ok_all else 'RESULT=FAIL\nREASON=One_or_more_build_or_audit_stages_failed\n') + 'DEPENDENCY_INDEPENDENCE=NOT_YET_VERIFIED\n')
    print('RESULT=' + ('PASS' if ok_all else 'FAIL'), flush=True)
    if ok_all:
        print('THETA_ROOT_BUILD_AND_NAMED_AXIOM_AUDIT=PASS', flush=True)
    return 0 if ok_all else 1


if __name__ == '__main__':
    try:
        sys.exit(run())
    except Exception as exc:
        print(f'RESULT=FAIL\nRUNNER_ERROR={exc}', file=sys.stderr, flush=True)
        sys.exit(1)
