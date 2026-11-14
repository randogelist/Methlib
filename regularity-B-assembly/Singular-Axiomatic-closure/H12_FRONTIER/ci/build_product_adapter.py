#!/usr/bin/env python3
"""External cached Lean build; exact checkpoint types and standard-only axioms."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'evidence' / 'product'


def run(args: list[str], path: Path) -> int:
    with path.open('w', encoding='utf-8') as output:
        process = subprocess.Popen(args, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True,
                                   encoding='utf-8', errors='replace')
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end='', flush=True)
            output.write(line)
        return process.wait()


def write_results(records: list[dict]) -> None:
    expected = [f'P{i:02d}' for i in range(1, 17)]
    complete = [r['id'] for r in records if r['status'] == 'COMPILE_AND_AUDIT_PASS']
    payload = {
        'schema_version': 1,
        'source_commit': os.environ.get('SOURCE_SHA'),
        'workflow_event_sha': os.environ.get('GITHUB_SHA'),
        'run_id': os.environ.get('GITHUB_RUN_ID'),
        'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
        'expected_checkpoints': expected,
        'compiled_and_audited_checkpoints': complete,
        'status': 'PASS' if complete == expected else 'INCOMPLETE_OR_FAILED',
        'completion_requires_scope_review': True,
        'entries': records,
    }
    (OUT / 'results.json').write_text(json.dumps(payload, indent=2)+'\n', encoding='utf-8')


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    cache = json.loads((ROOT / 'evidence/cache.json').read_text())
    if cache.get('project_cache') != 'RESTORED' or cache.get('dependency_cache') != 'RESTORED':
        raise RuntimeError('CACHED_RUN_REQUIRED')
    if not (ROOT / '.lake/build/lib/lean/SingularClosure/H12Frontier/ReplayClosure.olean').is_file():
        raise RuntimeError('COMPILED_BASE_CACHE_REQUIRED')
    plan = json.loads((ROOT / 'ci/product_plan.json').read_text(encoding='utf-8'))
    entries = plan['entries']
    expected = [f'P{i:02d}' for i in range(1, 17)]
    if [e['id'] for e in entries] != expected:
        raise RuntimeError('CHECKPOINT_LIST_MUST_EQUAL_P01_THROUGH_P16')

    proof_sources = sorted((ROOT / 'SingularClosure/H12Frontier').glob('Product*.lean'))
    if not proof_sources:
        raise RuntimeError('NO_PRODUCT_PROOF_SOURCES')
    for path in proof_sources:
        text = path.read_text(encoding='utf-8')
        if re.search(r'\b(sorry|admit|unsafe)\b', text):
            raise RuntimeError('FORBIDDEN_PROOF_TOKEN:'+str(path.relative_to(ROOT)))
        if re.search(r'^\s*axiom\s', text, re.MULTILINE):
            raise RuntimeError('NEW_AXIOM_DECLARATION:'+str(path.relative_to(ROOT)))

    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(ROOT.rglob('*.lean'))
              if '.lake' not in p.parts and 'evidence' not in p.parts}
    (OUT / 'source-sha256.json').write_text(json.dumps(hashes, indent=2, sort_keys=True)+'\n')
    for entry in entries:
        spec = json.loads((ROOT / entry['spec']).read_text())
        if set(spec.get('standard_axioms', [])) != {'propext','Classical.choice','Quot.sound'}:
            raise RuntimeError('INVALID_STANDARD_AXIOM_POLICY:'+entry['id'])
        if not spec.get('declarations'):
            raise RuntimeError('EMPTY_DECLARATION_LIST:'+entry['id'])
        for declaration in spec['declarations']:
            if declaration.get('additional_allowed_axioms') or declaration.get('required_axioms'):
                raise RuntimeError('CUSTOM_AXIOM_POLICY_FORBIDDEN:'+entry['id'])

    records: list[dict] = []
    builds: dict[str, tuple[int, str]] = {}
    write_results(records)
    for entry in entries:
        ident, module = entry['id'], entry['module']
        record = dict(entry, source_commit=os.environ.get('SOURCE_SHA'),
                      status='BUILD_FAILED', exact_type='NOT_RUN', axiom_audit='NOT_RUN')
        if module not in builds:
            filename = f'{ident}-build.log'
            builds[module] = (run(['lake','build',module], OUT/filename), filename)
        build_rc, build_log = builds[module]
        record['build_log'] = build_log
        if build_rc == 0:
            audit_log = OUT/f'{ident}-axioms.log'
            audit_rc = run(['lake','env','lean',entry['audit']], audit_log)
            if audit_rc == 0:
                audit_json = OUT/f'{ident}-audit.json'
                check_rc = run([sys.executable,'ci/check_axioms.py',str(audit_log),entry['spec']], audit_json)
                if check_rc == 0:
                    evidence = json.loads(audit_json.read_text())
                    record.update(status='COMPILE_AND_AUDIT_PASS',exact_type='PASS',
                                  axiom_audit='PASS_STANDARD_ONLY',
                                  audited_declarations=evidence['declarations'])
                else:
                    record['status'] = 'AUDIT_FAILED'
            else:
                record['status'] = 'EXACT_TYPE_OR_COMPILER_FAILED'
        records.append(record)
        write_results(records)
        print('PRODUCT_RESULT:'+json.dumps(record, sort_keys=True), flush=True)
        if record['status'] == 'COMPILE_AND_AUDIT_PASS':
            print('<=> '+ident, flush=True)
    failed = any(r['status'] != 'COMPILE_AND_AUDIT_PASS' for r in records)
    if not failed:
        entry_rc = run(['lake','env','lean','FRONTIER_H12_PRODUCT_ADAPTER_CHAIN.lean'],
                       OUT/'delivery-entrypoint.log')
        (OUT/'delivery-entrypoint.json').write_text(json.dumps({'exit_code':entry_rc,
            'source_commit':os.environ.get('SOURCE_SHA'),
            'status':'PASS' if entry_rc == 0 else 'FAIL'},indent=2)+'\n')
        failed = entry_rc != 0
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
