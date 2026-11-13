#!/usr/bin/env python3
"""Native Windows cached replay; never downloads or deletes a cache."""
from pathlib import Path
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def output(args):
    return subprocess.check_output(args, cwd=ROOT, text=True, encoding='utf-8').strip()

def main():
    if os.name != 'nt':
        raise SystemExit('NATIVE_WINDOWS_RUNNER_REQUIRED')
    if (ROOT/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.0':
        raise SystemExit('LEAN_TOOLCHAIN_MISMATCH')
    version = output(['lean','--version'])
    if 'version 4.33.0,' not in version:
        raise SystemExit('LEAN_VERSION_MISMATCH: '+version)
    mathlib = ROOT/'.lake/packages/mathlib'
    if output(['git','-C',str(mathlib),'rev-parse','HEAD']) != 'db584cd6d46c92f209a44c0f1c829460d327499d':
        raise SystemExit('MATHLIB_REVISION_MISMATCH')
    for path in [ROOT/'.lake/build/lib/lean/SingularClosure/H12Frontier/ReplayClosure.olean',mathlib/'.lake/build/lib/lean/Mathlib.olean']:
        if not path.is_file():
            raise SystemExit('REQUIRED_NATIVE_CACHE_MISSING: '+str(path))
    evidence=ROOT/'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence/'cache.json').write_text(json.dumps({'project_cache':'RESTORED','dependency_cache':'RESTORED','source':'existing_native_windows_cache','uncached_fallback':False},indent=2)+'\n')
    (evidence/'lean-version.txt').write_text(version+'\n')
    os.environ['SOURCE_SHA']=output(['git','rev-parse','HEAD'])
    return subprocess.call([sys.executable,'ci/build_product_adapter.py'],cwd=ROOT)

if __name__ == '__main__':
    raise SystemExit(main())
