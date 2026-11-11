#!/usr/bin/env python3
"""Build the extension DAG, then kernel-build and audit every required endpoint."""
import json
from functools import cache
from pathlib import Path
import re
import subprocess
import sys

ROOT_MODULE = 'SingularClosure.SmallDataClosure'
ROOT_DECLARATION = 'SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL'
STATUS_PATH = Path('evidence/critical-build-status.json')


def unique_names(values, label):
    if not isinstance(values, list) or not values:
        raise ValueError(label + ' must be a nonempty list')
    if any(not isinstance(x, str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', x)
           for x in values):
        raise ValueError(label + ' contains an invalid module name')
    if len(values) != len(set(values)):
        raise ValueError(label + ' contains duplicates')
    return values


def load_plan():
    modules = unique_names([x.strip() for x in Path('ci/critical_modules.txt').read_text(encoding='utf-8').splitlines()
                            if x.strip()], 'build modules')
    manifest = json.loads(Path('ci/critical_required_audits.json').read_text(encoding='utf-8'))
    if not isinstance(manifest, dict) or manifest.get('schema_version') != 1:
        raise ValueError('unsupported required-audit manifest schema')
    required = unique_names(manifest.get('required_modules'), 'required audits')
    if ROOT_MODULE not in required:
        raise ValueError('required audits omit the root endpoint: ' + ROOT_MODULE)
    unknown = set(required) - set(modules)
    if unknown:
        raise ValueError('required audits absent from build modules: ' + repr(sorted(unknown)))
    names = [x.rsplit('.', 1)[-1] for x in required]
    if len(names) != len(set(names)):
        raise ValueError('required audit basenames collide')
    directory = Path('ci/critical_audits')
    for suffix in ('.lean', '.json'):
        actual = {p.stem for p in directory.glob('*' + suffix) if p.is_file()}
        if actual != set(names):
            raise ValueError('audit ' + suffix + ' coverage mismatch: missing=' +
                             repr(sorted(set(names) - actual)) + ', extra=' +
                             repr(sorted(actual - set(names))))
    root_spec = json.loads((directory / 'SmallDataClosure.json').read_text(encoding='utf-8'))
    if not isinstance(root_spec, dict) or not any(
            isinstance(item, dict) and item.get('name') == ROOT_DECLARATION
            for item in root_spec.get('declarations', [])):
        raise ValueError('root audit omits the required declaration: ' + ROOT_DECLARATION)
    module_set = set(modules)
    deps = {}
    for module in modules:
        source = Path(module.replace('.', '/') + '.lean')
        imports = re.findall(r'^import\s+(\S+)', source.read_text(encoding='utf-8'), re.M)
        deps[module] = [x for x in imports if x in module_set]
    order, visiting, visited = [], set(), set()

    def visit(module):
        if module in visiting:
            raise ValueError('Import cycle: ' + module)
        if module in visited:
            return
        visiting.add(module)
        for dep in deps[module]:
            visit(dep)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for module in modules:
        visit(module)
    return order, deps, required


def run(command, log):
    with Path(log).open('w', encoding='utf-8') as output:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, encoding='utf-8', errors='replace', bufsize=1)
        for line in process.stdout:
            output.write(line)
            print(line, end='', flush=True)
        return process.wait() == 0


def write_status(result):
    STATUS_PATH.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')


def main():
    Path('evidence').mkdir(exist_ok=True)
    # Replace stale successful evidence before any validation or compiler call.
    result = {'status': 'FAIL', 'bulk_build': 'NOT_RUN', 'builds': {}, 'audits': {},
              'required_audits': [], 'audit_coverage': 'FAIL', 'errors': []}
    write_status(result)
    try:
        order, deps, required = load_plan()
        required_set = set(required)
        result['required_audits'] = required
        bulk = run(['lake', 'build', *order], 'evidence/critical-build.log')
        result['bulk_build'] = 'PASS' if bulk else 'FAIL'
        status = result['builds'] = {module: 'PASS' if bulk else 'UNVERIFIED' for module in order}
        audits = result['audits']
        if not bulk:
            # Diagnostics only identify blockers; they cannot establish success.
            log_text = Path('evidence/critical-build.log').read_text(encoding='utf-8')
            for source in re.findall(r'^error: (SingularClosure/[^:\n]+)\.lean:', log_text, re.M):
                module = source.replace('/', '.')
                if module in status:
                    status[module] = 'FAIL'

        @cache
        def ancestors(module):
            answer = set()
            for dep in deps[module]:
                answer.add(dep)
                answer.update(ancestors(dep))
            return answer

        for module in order:
            if module not in required_set:
                continue
            name = module.rsplit('.', 1)[-1]
            audit = Path(f'ci/critical_audits/{name}')
            dependency_closure = ancestors(module)
            blockers = sorted(d for d in dependency_closure | {module} if status[d] == 'FAIL')
            if blockers:
                audits[module] = 'BLOCKED'
                print(json.dumps({'module': module, 'audit': 'BLOCKED', 'dependencies': blockers}), flush=True)
                continue
            # A successful target build validates its dependency closure at this
            # source snapshot. Existing .olean files alone establish no success.
            success = run(['lake', 'build', module], f'evidence/{name}-build.log')
            if not success:
                status[module] = 'FAIL'
                audits[module] = 'FAIL'
                continue
            for validated in dependency_closure | {module}:
                status[validated] = 'PASS'
            log = f'evidence/{name}-axioms.log'
            checked = run(['lake', 'env', 'lean', str(audit.with_suffix('.lean'))], log)
            if checked:
                checked = run([sys.executable, 'ci/check_axioms.py', log,
                               str(audit.with_suffix('.json'))], f'evidence/{name}-audit.json')
            audits[module] = 'PASS' if checked else 'FAIL'
        coverage = bool(required_set) and set(audits) == required_set
        result['audit_coverage'] = 'PASS' if coverage else 'FAIL'
        if not coverage:
            result['errors'].append('final audit keys do not match the required manifest')
        if bulk and coverage and set(status) == set(order) and all(
                s == 'PASS' for s in status.values()) and all(audits[m] == 'PASS' for m in required):
            result['status'] = 'PASS'
    except (OSError, ValueError, TypeError, KeyError) as error:
        result['errors'].append(str(error))
    write_status(result)
    print(json.dumps(result), flush=True)
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
