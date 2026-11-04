#!/usr/bin/env python3
"""Append a separately hashed candidate to a verified copied lane, no Lean."""
import json, shutil, subprocess, sys
from pathlib import Path
lane = Path(sys.argv[1]).resolve(strict=True)
base = Path(__file__).resolve().parent
name = 'HVRCompactCorrelationOrdinaryWave'
src = base / (name + '.lean')
dst = lane / 'sources' / (name + '.lean')
if dst.exists(): raise SystemExit('candidate module already exists')
plan_path = lane / 'plan.json'
plan = json.loads(plan_path.read_text(encoding='utf-8'))
if any(x['module'] == name for x in plan): raise SystemExit('duplicate candidate module')
shutil.copyfile(src, dst)
plan.append({'module':name, 'theorems':[name + '.fourierInv_correlation_eq_seed_transform_sq']})
plan_path.write_text(json.dumps(plan, indent=2) + '\n', encoding='utf-8')
subprocess.run([sys.executable, str(lane / 'freeze_manifest.py')], cwd=lane, check=True)
subprocess.run([sys.executable, str(lane / 'run_linux.py'), '--check-plan'], cwd=lane, check=True)
print('ORDINARY_WAVE_CANDIDATE_APPENDED')
