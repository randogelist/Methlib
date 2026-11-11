#!/usr/bin/env python3
"""Build the declared extension DAG, audit successful endpoints, and retain diagnostics."""
import json
from pathlib import Path
import re
import subprocess
import sys

modules = [x.strip() for x in Path('ci/critical_modules.txt').read_text().splitlines() if x.strip()]
module_set = set(modules)
deps = {}
for module in modules:
    source = Path(module.replace('.', '/') + '.lean')
    imports = re.findall(r'^import\s+(\S+)', source.read_text(), re.M)
    deps[module] = [x for x in imports if x in module_set]
order, visiting, visited = [], set(), set()
def visit(module):
    if module in visiting:
        raise RuntimeError('Import cycle: ' + module)
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
Path('evidence').mkdir(exist_ok=True)
status, audits = {}, {}
def run(command, log):
    with Path(log).open('w') as output:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, bufsize=1)
        for line in process.stdout:
            output.write(line)
            print(line, end='', flush=True)
        return process.wait() == 0
for module in order:
    name = module.rsplit('.', 1)[-1]
    blockers = [d for d in deps[module] if status[d] != 'PASS']
    if blockers:
        status[module] = 'BLOCKED'
        print(json.dumps({'module': module, 'status': 'BLOCKED', 'dependencies': blockers}), flush=True)
        continue
    success = run(['lake', 'build', module], f'evidence/{name}-build.log')
    status[module] = 'PASS' if success else 'FAIL'
    print(json.dumps({'module': module, 'status': status[module]}), flush=True)
    audit = Path(f'ci/critical_audits/{name}')
    if success and audit.with_suffix('.lean').is_file():
        log = f'evidence/{name}-axioms.log'
        checked = run(['lake', 'env', 'lean', str(audit.with_suffix('.lean'))], log)
        if checked:
            checked = run([sys.executable, 'ci/check_axioms.py', log,
                           str(audit.with_suffix('.json'))], f'evidence/{name}-audit.json')
        audits[module] = 'PASS' if checked else 'FAIL'
Path('evidence/critical-build-status.json').write_text(
    json.dumps({'builds': status, 'audits': audits}, indent=2) + '\n')
sys.exit(0 if all(s == 'PASS' for s in status.values()) and
             all(s == 'PASS' for s in audits.values()) else 1)
