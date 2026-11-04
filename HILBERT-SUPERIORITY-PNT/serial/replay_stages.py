#!/usr/bin/env python3
"""Replay against a disposable Git checkout. A failed stage stops the sequence."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from verify_stage import PKG, ROOT, external, git, need, read_plan, verify_sources

def execute(cwd,*args):
    subprocess.run(list(args),cwd=cwd,check=True)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,default=Path.cwd())
    p.add_argument('--stages',type=Path,required=True)
    p.add_argument('--catalog',type=Path,required=True)
    p.add_argument('--objects',type=Path,required=True)
    p.add_argument('--evidence',type=Path,required=True)
    p.add_argument('--source-only',action='store_true')
    p.add_argument('--prefix',type=int,help='check only the first N stages; record PARTIAL scope')
    args=p.parse_args();repo=args.repo.resolve();spec=args.stages.resolve()
    spec_root=spec.parent;data=json.loads(spec.read_text());catalog=json.loads(args.catalog.read_text())
    stages=data['stages'];base=data['base']
    need(bool(re.fullmatch('[0-9a-f]{40}',base)) and stages,'missing pinned base / stages')
    need(len({s['id'] for s in stages})==len(stages),'duplicate stage IDs')
    need(len({s['target'] for s in stages})==len(stages),'each target must have exactly one stage')
    need(all(re.fullmatch(r'[A-Za-z0-9_-]{1,90}',s['id']) for s in stages),'invalid stage ID')
    if args.prefix is not None: need(0<args.prefix<=len(stages),'invalid replay prefix')
    queued=stages[:args.prefix]; complete=len(queued)==len(stages)
    ev=args.evidence.resolve();ev.mkdir(parents=True,exist_ok=False)
    partial=[]
    track=dict(head=git(repo,'rev-parse','HEAD').decode().strip(),base=base,stage_count=len(stages),requested_count=len(queued),source_only=args.source_only)
    result_file=ev/'result.txt'
    try:
        with tempfile.TemporaryDirectory() as td:
            w=Path(td)
            execute(None,'git','clone','--local','--no-checkout','--quiet',str(repo),str(w))
            execute(w,'git','-c','core.autocrlf=false','checkout','--quiet','--detach',base)
            for i,s in enumerate(queued):
                work=dict(s);work['final_root']=complete and i==len(queued)-1
                print('STAGE_BEGIN='+s['id'],flush=True)
                d=ev/s['id'];d.mkdir()
                patch=(spec_root/s['patch']).resolve()
                need(patch.is_relative_to(spec_root) and patch.is_file(),'patch must reside inside the serial package')
                bp=git(w,'rev-parse','HEAD').decode().strip()
                execute(w,'git','apply','--index','--check',str(patch))
                execute(w,'git','apply','--index',str(patch))
                # Patches contain only declarative edits to Lean project source. Infrastructure comes from this harness.
                touched=set(git(w,'diff','--cached','--name-only').decode().splitlines())
                sources={f'{PKG}/{m}.lean' for m in s['modules']}
                integration=f'{PKG}/zetahyperbolic-integration'
                metadata={f'{PKG}/run.ps1',f'{PKG}/branch_sources.sha256',f'{integration}/plan.json',f'{integration}/sources.sha256'}
                metadata|={f'{PKG}/Audit_{m}.lean' for m in s['modules']}
                metadata|={f'{integration}/sources/{m}.lean' for m in s['modules']}
                need(sources<=touched and touched<=sources|metadata,f'unexpected or missing staged paths: {touched^sources}')
                execute(w,'git','-c','user.name=PNT CI','-c','user.email=ci@localhost','-c','commit.gpgsign=false','-c','core.hooksPath=/dev/null','commit','--quiet','-m','Replay '+s['id'])
                plan=read_plan(w/PKG)
                counts=verify_sources(w,bp,work,catalog,plan)
                info=dict(id=s['id'],target=s['target'],parent=bp,post=git(w,'rev-parse','HEAD').decode().strip(),patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),direct_source_counts=counts)
                if not args.source_only: info.update(external(w,d,args.objects.resolve(),work,plan))
                (d/'summary.json').write_text(json.dumps(info,indent=2))
                stamp='SOURCE_CHECK_PASS' if args.source_only else 'STAGE_BUILD_AND_NAMED_AUDIT_PASS'
                (d/'result.txt').write_text('RESULT='+stamp+'\n')
                partial.append(dict(id=s['id'],target=s['target'],result=stamp));print(f'STAGE_RESULT={s["id"]}|{stamp}',flush=True)
            if complete:
                # Every canonical production module in aggregate HEAD must equal its exact replay postimage.
                for mod in read_plan(w/PKG):
                    f=f'{PKG}/{mod}.lean'
                    need((w/f).read_bytes()==git(repo,'show',f'HEAD:{f}'),'aggregate head differs from replay: '+f)
                if not args.source_only:need(info.get('root_audited',False),'missing final root audit')
        result=('SERIES' if complete else 'PREFIX')+('_SOURCE_CHECK_PASS' if args.source_only else '_KERNEL_AND_AXIOM_AUDIT_PASS')
        result_file.write_text('RESULT='+result+'\n');print('RESULT='+result)
    except Exception as exc:
        result_file.write_text('RESULT=FAIL\nERROR='+str(exc)+'\n');raise
    finally:
        track['stages_completed']=partial;(ev/'summary.json').write_text(json.dumps(track,indent=2))
if __name__=='__main__':main()
