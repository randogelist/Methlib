#!/usr/bin/env python3
"""Append separately hashed candidates to a frozen copied lane; no Lean."""
import json, shutil, subprocess, sys
from pathlib import Path
lane = Path(sys.argv[1]).resolve(strict=True)
base = Path(__file__).resolve().parent
entries = [('HVROneDimensionalCompactDecay',['phase_integral_mul_eq_neg_derivative_integral','phase_integral_derivative_bound']),('HVRCompactSeedIntervalDecay',['seed_deriv_integrable','phase_hasDerivAt','seed_phase_first_derivative_bound'])]
plan_path = lane / 'plan.json'
plan = json.loads(plan_path.read_text(encoding='utf-8'))
for name, theorems in entries:
    dst = lane / 'sources' / (name + '.lean')
    if dst.exists() or any(x['module'] == name for x in plan): raise SystemExit('duplicate candidate: '+name)
    shutil.copyfile(base / (name + '.lean'), dst)
    plan.append({'module':name, 'theorems':[name + '.' + x for x in theorems]})
plan_path.write_text(json.dumps(plan, indent=2) + '\n', encoding='utf-8')
subprocess.run([sys.executable, str(lane / 'freeze_manifest.py')], cwd=lane, check=True)
subprocess.run([sys.executable, str(lane / 'run_linux.py'), '--check-plan'], cwd=lane, check=True)
print('COMPACT_SEED_DECAY_CANDIDATES_APPENDED')
