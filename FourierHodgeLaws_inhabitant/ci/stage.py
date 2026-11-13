#!/usr/bin/env python3
"""Stage the pinned source package without executing Lean or deleting caches."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import urllib.request
import zipfile

UPSTREAM = '9f5500cd5dadc351ab3ec98db09dccaa9a22eb25'
REPOSITORY = 'randogelist/NSE---MAXWELL---GR---QFT'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--upstream-root', type=Path)
    p.add_argument('--overlay', type=Path, default=Path(__file__).resolve().parent.parent)
    p.add_argument('--package', type=Path, required=True)
    a=p.parse_args()
    overlay=a.overlay.resolve(); package=a.package.resolve()
    if overlay == package or overlay in package.parents and '.work' not in package.parts:
        raise ValueError('Use a distinct staging directory.')
    package.mkdir(parents=True, exist_ok=True)
    evidence=package/'hodge-evidence'; evidence.mkdir(exist_ok=True)
    if a.upstream_root:
        upstream=a.upstream_root.resolve()
        actual=subprocess.check_output(['git','-C',str(upstream),'rev-parse','HEAD'], text=True).strip()
        if actual != UPSTREAM:
            raise ValueError(f'Unexpected upstream commit {actual}')
        src=upstream/'Fefferman_adapter'
        shutil.copytree(src, package, dirs_exist_ok=True, ignore=shutil.ignore_patterns('.lake','artifacts'))
    else:
        archive=overlay/'.work'/f'{UPSTREAM}.zip'
        archive.parent.mkdir(exist_ok=True)
        if not archive.is_file():
            urllib.request.urlretrieve(f'https://github.com/{REPOSITORY}/archive/{UPSTREAM}.zip', archive)
        with zipfile.ZipFile(archive) as z:
            roots={PurePosixPath(n).parts[0] for n in z.namelist() if n}
            if len(roots)!=1:
                raise ValueError('Unexpected archive roots')
            prefix=next(iter(roots))+'/Fefferman_adapter/'
            count=0
            for entry in z.infolist():
                if not entry.filename.startswith(prefix) or entry.is_dir():
                    continue
                rel=PurePosixPath(entry.filename[len(prefix):])
                if rel.is_absolute() or any(x in ('..','.git','.lake') for x in rel.parts):
                    raise ValueError('Unsafe archive entry')
                dst=package/str(rel); dst.parent.mkdir(parents=True,exist_ok=True)
                dst.write_bytes(z.read(entry)); count+=1
            if count<1000:
                raise ValueError('Incomplete pinned source archive')
    upstream_hashes={p.relative_to(package).as_posix():sha(p) for p in package.rglob('*')
                     if p.is_file() and not any(x in ('.lake','hodge-evidence') for x in p.relative_to(package).parts)}
    allowed=('FourierHodgeLaws','ci')
    overlay_hashes={}
    for src in sorted(overlay.rglob('*')):
        if not src.is_file(): continue
        rel=src.relative_to(overlay)
        if any(x in ('.work','__pycache__') for x in rel.parts): continue
        if len(rel.parts)>1 and rel.parts[0] not in allowed: continue
        if len(rel.parts)==1 and not (src.suffix in ('.lean','.json','.txt','.md','.cmd','.sh') or src.name=='lean-toolchain'): continue
        dst=package/rel; dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(src,dst); overlay_hashes[rel.as_posix()]=sha(dst)
    stage={'upstream_repository':REPOSITORY,'upstream_commit':UPSTREAM,
           'overlay_sha':__import__('os').environ.get('GITHUB_SHA'),
           'upstream_files':upstream_hashes,'overlay_files':overlay_hashes}
    (evidence/'staging.json').write_text(json.dumps(stage,indent=2)+'\n')
    print(json.dumps({'staged_package':str(package),'upstream_files':len(upstream_hashes),
                      'overlay_files':len(overlay_hashes),'upstream_commit':UPSTREAM}))

if __name__=='__main__': main()
