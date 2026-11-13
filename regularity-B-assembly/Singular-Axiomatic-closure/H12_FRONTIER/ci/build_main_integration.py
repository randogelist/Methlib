#!/usr/bin/env python3
"""Audit the exact merged candidate using restored Lean 4.33.0 caches.

No source regeneration, dependency update, cache deletion, or uncached bootstrap.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'evidence' / 'main-integration'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB_REV = 'db584cd6d46c92f209a44c0f1c829460d327499d'
CHECKPOINTS = [f'P{i:02d}' for i in range(1, 17)]
BASELINE = [
    {'id': 'FRONTIER_NATIVE', 'module': 'SingularClosure.H12Frontier.Root',
     'audit': 'ci/frontier_audits/E13.lean', 'spec': 'ci/frontier_audits/E13.json',
     'theorem': 'SingularClosure.H12Frontier.FRONTIER_H12_NATIVE'},
    {'id': 'FRONTIER_PUBLIC', 'module': 'SingularClosure.H12Frontier.Root',
     'audit': 'ci/frontier_audits/E14.lean', 'spec': 'ci/frontier_audits/E14.json',
     'theorem': 'SingularClosure.H12Frontier.FRONTIER_H12'},
    {'id': 'BASE_REGRESSION', 'module': 'SingularClosure.SmallDataClosure',
     'audit': 'ci/critical_audits/SmallDataClosure.lean',
     'spec': 'ci/critical_audits/SmallDataClosure.json',
     'theorem': 'SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL'},
]


def run(args: list[str], log: Path) -> int:
    with log.open('w', encoding='utf-8') as output:
        process = subprocess.Popen(args, cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace')
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end='', flush=True)
            output.write(line)
        return process.wait()


def source_hashes() -> dict[str, str]:
    paths = [p for p in ROOT.rglob('*.lean')
             if not any(part in {'.lake', '.git', 'evidence'} for part in p.relative_to(ROOT).parts)]
    paths += [ROOT / name for name in ['lean-toolchain', 'lake-manifest.json',
        'lakefile.toml', 'ci/build_main_integration.py', 'ci/build_product_adapter.py',
        'ci/check_axioms.py', 'ci/product_plan.json']]
    paths += list((ROOT / 'ci/product_audits').glob('*.json'))
    paths += [ROOT / item['spec'] for item in BASELINE]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths))}


def require_standard_spec(spec: dict, expected_names: list[str]) -> None:
    if spec.get('schema_version') != 1 or set(spec.get('standard_axioms', [])) != STANDARD_AXIOMS:
        raise RuntimeError('STANDARD_AXIOM_SPEC_REQUIRED')
    declarations = spec.get('declarations', [])
    if [d.get('name') for d in declarations] != expected_names:
        raise RuntimeError('AUDIT_DECLARATIONS_MISMATCH')
    for declaration in declarations:
        if declaration.get('additional_allowed_axioms') or declaration.get('required_axioms'):
            raise RuntimeError('CUSTOM_AXIOM_POLICY_FORBIDDEN')
        if declaration.get('exact_type_marker') != 'EXACT_TYPE_PASS:' + declaration['name']:
            raise RuntimeError('EXACT_TYPE_MARKER_MISMATCH')


def validate_product_results(product: dict, delivery: dict, source: str, plan: dict) -> int:
    if product.get('status') != 'PASS' or product.get('source_commit') != source:
        raise RuntimeError('PRODUCT_STATUS_OR_SOURCE_MISMATCH')
    if product.get('compiled_and_audited_checkpoints') != CHECKPOINTS:
        raise RuntimeError('PRODUCT_CHECKPOINTS_INCOMPLETE')
    if delivery.get('status') != 'PASS' or delivery.get('exit_code') != 0:
        raise RuntimeError('DELIVERY_ENTRYPOINT_FAILED')
    if delivery.get('source_commit') != source:
        raise RuntimeError('DELIVERY_SOURCE_MISMATCH')
    entries, targets = product.get('entries', []), plan.get('entries', [])
    if len(entries) != 16 or [e.get('id') for e in targets] != CHECKPOINTS:
        raise RuntimeError('PRODUCT_PLAN_OR_ENTRY_COUNT_MISMATCH')
    total = 0
    for record, target in zip(entries, targets, strict=True):
        if record.get('id') != target['id'] or record.get('source_commit') != source:
            raise RuntimeError('CHECKPOINT_ID_OR_SOURCE_MISMATCH')
        if record.get('status') != 'COMPILE_AND_AUDIT_PASS' or record.get('exact_type') != 'PASS' or record.get('axiom_audit') != 'PASS_STANDARD_ONLY':
            raise RuntimeError('CHECKPOINT_NOT_COMPILED_AND_AUDITED')
        actual = record.get('audited_declarations', [])
        if [d.get('name') for d in actual] != target['declarations']:
            raise RuntimeError('CHECKPOINT_DECLARATION_MISMATCH')
        for declaration in actual:
            if not set(declaration.get('axioms', [])) <= STANDARD_AXIOMS:
                raise RuntimeError('UNAPPROVED_PRODUCT_AXIOM')
        total += len(actual)
    if total != 38:
        raise RuntimeError('EXPECTED_38_PRODUCT_THEOREMS')
    return total


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    source = os.environ.get('SOURCE_SHA', '')
    result = {'schema_version': 1, 'source_commit': source,
        'workflow_event_sha': os.environ.get('GITHUB_SHA'),
        'head_commit': os.environ.get('HEAD_SHA'),
        'target_base_commit': os.environ.get('BASE_SHA'),
        'frontier_base_commit': os.environ.get('BASE_SOURCE_SHA'),
        'run_id': os.environ.get('GITHUB_RUN_ID'),
        'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
        'status': 'INCOMPLETE_OR_FAILED', 'baseline': [],
        'product_status': 'NOT_RUN', 'errors': []}

    def save() -> None:
        (OUT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')

    save()
    try:
        if not re.fullmatch(r'[0-9a-f]{40}', source):
            raise RuntimeError('EXACT_SOURCE_SHA_REQUIRED')
        if os.environ.get('GITHUB_SHA') != source:
            raise RuntimeError('MERGED_CANDIDATE_SOURCE_REQUIRED')
        cache = json.loads((ROOT / 'evidence/cache.json').read_text())
        if cache.get('project_cache') != 'RESTORED' or cache.get('dependency_cache') != 'RESTORED':
            raise RuntimeError('RESTORED_DEPENDENCY_AND_PROJECT_CACHES_REQUIRED')
        sentinels = [ROOT / '.lake/build/lib/lean/SingularClosure/SmallDataClosure.olean',
                     ROOT / '.lake/build/lib/lean/SingularClosure/H12Frontier/ReplayClosure.olean']
        if not any(p.is_file() and p.stat().st_size for p in sentinels):
            raise RuntimeError('CACHED_BASE_OR_FRONTIER_BOOTSTRAP_REQUIRED')
        if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.0':
            raise RuntimeError('LEAN_TOOLCHAIN_MISMATCH')
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        mathlib_entries = [p for p in manifest['packages'] if p.get('name') == 'mathlib']
        if len(mathlib_entries) != 1 or mathlib_entries[0].get('rev') != MATHLIB_REV:
            raise RuntimeError('MATHLIB_LOCKFILE_MISMATCH')
        if run(['lean', '--version'], OUT / 'lean-version.txt'):
            raise RuntimeError('LEAN_VERSION_COMMAND_FAILED')
        if 'version 4.33.0,' not in (OUT / 'lean-version.txt').read_text():
            raise RuntimeError('LEAN_COMPILER_MISMATCH')
        if run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], OUT / 'mathlib-revision.txt'):
            raise RuntimeError('MATHLIB_REVISION_COMMAND_FAILED')
        if (OUT / 'mathlib-revision.txt').read_text().strip() != MATHLIB_REV:
            raise RuntimeError('MATHLIB_CHECKOUT_MISMATCH')
        mathlib_object = ROOT / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
        if not mathlib_object.is_file() or not mathlib_object.stat().st_size:
            raise RuntimeError('COMPILED_MATHLIB_CACHE_REQUIRED')

        before = source_hashes()
        (OUT / 'source-sha256.json').write_text(json.dumps(before, indent=2, sort_keys=True) + '\n')
        result['verified_cache'] = cache
        result['source_hash_count'] = len(before)
        builds = {}
        for target in BASELINE:
            spec = json.loads((ROOT / target['spec']).read_text())
            require_standard_spec(spec, [target['theorem']])
            ident, module = target['id'], target['module']
            record = dict(target, source_commit=source, status='BUILD_FAILED')
            if module not in builds:
                builds[module] = run(['lake', 'build', module], OUT / (ident + '-build.log'))
            if builds[module] == 0:
                log = OUT / (ident + '-axioms.log')
                if run(['lake', 'env', 'lean', target['audit']], log) == 0:
                    audit_path = OUT / (ident + '-audit.json')
                    if run([sys.executable, 'ci/check_axioms.py', str(log), target['spec']], audit_path) == 0:
                        audit_result = json.loads(audit_path.read_text())
                        if audit_result.get('status') != 'PASS':
                            raise RuntimeError('BASELINE_AUDIT_STATUS_MISMATCH')
                        record.update(status='PASS', exact_type='PASS', axiom_audit='PASS_STANDARD_ONLY',
                                      audited_declarations=audit_result['declarations'])
                    else:
                        record['status'] = 'AXIOM_AUDIT_FAILED'
                else:
                    record['status'] = 'EXACT_TYPE_OR_COMPILER_FAILED'
            result['baseline'].append(record)
            save()
            print('MAIN_BASELINE_RESULT:' + json.dumps(record, sort_keys=True), flush=True)
        if any(record['status'] != 'PASS' for record in result['baseline']):
            raise RuntimeError('BASELINE_REGRESSION_FAILED')

        if run([sys.executable, 'ci/build_product_adapter.py'], OUT / 'product-run.log'):
            raise RuntimeError('PRODUCT_ADAPTER_RUN_FAILED')
        product = json.loads((ROOT / 'evidence/product/results.json').read_text())
        delivery = json.loads((ROOT / 'evidence/product/delivery-entrypoint.json').read_text())
        plan = json.loads((ROOT / 'ci/product_plan.json').read_text())
        total = validate_product_results(product, delivery, source, plan)
        if source_hashes() != before:
            raise RuntimeError('PROOF_INPUTS_CHANGED_DURING_RUN')
        result.update(status='PASS', product_status='PASS', product_checkpoints=16,
            product_theorem_audits=total, baseline_theorem_audits=3,
            delivery_entrypoint='PASS', source_hashes_unchanged=True,
            additional_allowed_axioms=[])
        save()
        print('MAIN_INTEGRATION_PASS:' + source, flush=True)
        return 0
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        result['errors'].append(str(error))
        save()
        print('MAIN_INTEGRATION_FAIL:' + str(error), flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
