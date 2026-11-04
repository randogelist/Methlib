#!/usr/bin/env python3
"""Verify one PNT source exchange and its affected theorems on a cached external Linux runner."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from stage_trace import trace_lines

MATHLIB = 'fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0'
PKG = 'HILBERT-SUPERIORITY-PNT'
ROOT = 'HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one'
ROOT_MODULE = 'HVR_PrimeDensity_FinalRoot'
ALLOWED = {'propext','Classical.choice','Quot.sound'}
MOD = re.compile(r'[A-Za-z][\w]*\Z')
NAME = re.compile(r"[\w']+(?:\.[\w']+)+\Z")
TOKEN = re.compile(r"[\w']+(?:\.[\w']+)*")
EXT = ('.olean','.olean.private','.olean.server','.ir','.ilean')

def need(test, message):
    if not test: raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle,'sha256').hexdigest()

def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()

def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args])

def code(data):
    # Discard nested Lean comments, string literals and editor/inspection commands.
    s=data.decode('utf8'); out=[]; i=depth=0; quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1;i+=2
            elif s.startswith('-/',i): depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif quoted:
            if s[i]=='\\':i+=2
            else:
                if s[i]=='"':quoted=False
                if s[i]=='\n':out.append('\n')
                i+=1
        elif s.startswith('/-',i):depth=1;out.append(' ');i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':quoted=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    need(not depth and not quoted,'unclosed comment/string')
    return re.sub(r'^\s*(?:#(?:check|print|eval|reduce)|import|open|namespace|end)\b[^\n]*',' ',''.join(out),flags=re.M)

def read_plan(pkg):
    t=(pkg/'run.ps1').read_text()
    section=re.search(r'(?ms)^  \$plan = @\(\s*\n(.*?)^  \)',t)[1]
    plan={}
    for row in section.splitlines():
        if not row.strip():continue
        mod,deps,names=re.fullmatch(r"\s*@\{ module = '([^']+)'; deps = @\((.*?)\); names = @\((.*?)\) \},?",row).groups()
        need(mod not in plan and MOD.fullmatch(mod),'invalid module '+mod)
        plan[mod]=(re.findall(r"'([^']+)'",deps),re.findall(r"'([^']+)'",names))
    for mod,(deps,names) in plan.items():
        # Actual local imports may be permitted earlier than their old order; DFS below performs scheduling.
        src=(pkg/(mod+'.lean')).read_text()
        incl={q for ln in re.findall(r'(?m)^\s*(?:(?:public|meta)\s+)*import\s+([^\n-]+)',src) for q in ln.split() if q in plan}
        # Per-target patches contain only source. Derive new local edges directly,
        # preserving the base's additional explicit ordering constraints.
        deps.extend(sorted(incl-set(deps)))
        need(all(q in plan for q in deps),'missing dependency')
    return plan

def verify_sources(repo,base,spec,catalog,plan):
    target=spec['target']; expected=spec['modules']
    need(target in catalog and len(expected)>0,'missing tracked target / module')
    diff=git(repo,'diff','--name-only',base,'HEAD','--',PKG).decode().splitlines()
    changed={Path(p).stem for p in diff if Path(p).parent==Path(PKG) and p.endswith('.lean') and Path(p).stem in plan}
    need(changed==set(expected),f'changed canonical modules {changed} != {set(expected)}')
    need(bool(spec['edges']),'at least one caller -> native theorem required')
    aliases={}
    for key,forms in catalog.items():
        for form in forms:
            need(form not in aliases,'ambiguous tracked alias '+form);aliases[form]=key
    counts={}
    for mod,rec in expected.items():
        need(MOD.fullmatch(mod) and mod in plan,'invalid module '+mod)
        path=f'{PKG}/{mod}.lean'; before=git(repo,'show',f'{base}:{path}');after=(repo/path).read_bytes()
        need(blob(before)==rec['old'] and blob(after)==rec['new'],'source SHA mismatch '+mod)
        need(after==git(repo,'show',f'HEAD:{path}'),'working source differs from HEAD')
        inputs=[TOKEN.findall(code(s)) for s in (before,after)]
        for k,forms in catalog.items():
            delta=[sum(any(t==x or t.startswith(x+'.') for x in forms) for t in tokens) for tokens in inputs]
            if k==target:
                need(delta[0]>=delta[1] and delta[1]==0,f'unexchanged call {k} in {mod}');counts[mod]=delta
            else:need(delta[0]==delta[1],f'second tracked target changed: {k} in {mod}')
    need(sum(v[0] for v in counts.values())>0,'target had no old calls')
    for edge in spec['edges']:
        need(set(edge)=={'module','caller','helper'} and edge['module'] in expected,'invalid edge')
        need(NAME.fullmatch(edge['caller']) and NAME.fullmatch(edge['helper']) and edge['caller']!=edge['helper'],'invalid declarations')
    trace_lines(spec)  # Validate the kernel-trace specification even for source-only inspection.
    return counts

def closure(plan,seeds):
    visited=set();active=set();order=[]
    def visit(m):
        need(m not in active,'cyclic local dependency '+m)
        if m in visited:return
        active.add(m)
        for d in plan[m][0]:visit(d)
        active.remove(m);visited.add(m);order.append(m)
    for m in seeds:visit(m)
    return order

def verify_audits(output,names):
    for n in names:
        found=re.findall(r"'"+re.escape(n)+r"' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",output,re.S)
        need(len(found)==1,'missing or duplicated audit '+n)
        terms=found[0]
        if '[' in terms:
            axioms={s.strip() for s in terms.split('[',1)[1][:-1].split(',') if s.strip()}
            need(axioms<=ALLOWED,f'unapproved axioms {n} {axioms-ALLOWED}')

def external(repo, ev, obj_cache, spec,plan):
    pkg=repo/PKG
    ml=Path(os.environ['MATHLIB_CACHE_ROOT']).resolve()
    need(git(ml,'rev-parse','HEAD').decode().strip()==MATHLIB,'Mathlib pin mismatch')
    lean=Path(os.environ['LEAN_EXE']).resolve()
    version=subprocess.check_output([lean,'--version'],text=True).strip()
    need(version.startswith('Lean (version 4.34.0-rc1,') and 'linux' in version.lower(),'Linux RC1 required')
    witness=ml/'.lake/build/lib/lean/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.olean'
    context=[file_sha(lean),version,MATHLIB,file_sha(ml/'lake-manifest.json'),file_sha(witness)]
    libdirs=[ml/'.lake/build/lib/lean',*sorted((ml/'.lake/packages').glob('*/.lake/build/lib/lean'))]
    obj=ev/'olean';obj.mkdir()
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[obj,*libdirs]))
    def invoke(args,log):
        result=subprocess.run([lean,*map(str,args)],cwd=pkg,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (ev/(log+'.log')).write_text(result.stdout)
        if result.returncode: print(result.stdout,flush=True);raise RuntimeError(f'{log}: {result.returncode}')
        return result.stdout
    force=set(spec['modules'])
    if spec.get('final_root'):force.add(ROOT_MODULE)
    order=closure(plan,sorted(force));keys={};state={};built=[];reused=[]
    obj_cache.mkdir(parents=True,exist_ok=True)
    for m in order:
        fp=sha(json.dumps([context,m,file_sha(pkg/(m+'.lean')),[keys[d] for d in plan[m][0]]]).encode())
        slot=obj_cache/fp; receipt=slot/'objects.json'
        hit=False
        if m not in force and receipt.is_file():
            recorded=json.loads(receipt.read_text())
            if isinstance(recorded,dict) and '.olean' in recorded and set(recorded)<=set(EXT):
                hit=all((slot/(m+e)).is_file() and file_sha(slot/(m+e))==h for e,h in recorded.items())
                if hit:
                    for e in recorded:shutil.copyfile(slot/(m+e),obj/(m+e))
        if hit:reused.append(m)
        else:
            invoke(['-o',obj/(m+'.olean'),m+'.lean'],'build_'+m);built.append(m)
            need((obj/(m+'.olean')).is_file(),'no output '+m)
            recorded={e:file_sha(obj/(m+e)) for e in EXT if (obj/(m+e)).is_file()}
            if not slot.exists():
                with tempfile.TemporaryDirectory(dir=obj_cache) as td:
                    out=Path(td)/'entry';out.mkdir()
                    for e in recorded:shutil.copyfile(obj/(m+e),out/(m+e))
                    (out/'objects.json').write_text(json.dumps(recorded))
                    try:out.rename(slot)
                    except OSError:
                        if not slot.is_dir():raise
        keys[m]=sha(json.dumps([fp,recorded],sort_keys=True).encode());state[m]=dict(key=fp,objects=recorded,cache='hit' if hit else 'fresh')
    # Include every new public theorem, not just those mentioned in the stage manifest.
    publics=[]
    for m in spec['modules']:
        raw=(pkg/(m+'.lean')).read_text()
        ns=re.findall(r'^namespace ([\w.]+)\s*$',raw,re.M)
        if len(ns)==1:
            publics.extend(ns[0]+'.'+n for n in re.findall(r'^(?:noncomputable\s+)?(?:theorem|lemma)\s+([\w\']+)',raw,re.M))
        else:need(m in spec.get('audits',{}),'explicit audit list required for multi-namespace source '+m)
    explicit=[n for names in spec.get('audits',{}).values() for n in names]
    names=list(dict.fromkeys([n for m in sorted(force) for n in plan[m][1]]+publics+explicit+[n for e in spec['edges'] for n in [e['caller'],e['helper']]]))
    need(all(NAME.fullmatch(n) for n in names),'unrecognized named audit')
    audit=['import '+m for m in sorted(force)]+['import Mathlib','import ImportGraph.Imports.RequiredModules','import ImportGraph.Lean.Environment','open Lean Elab Command']
    if spec.get('final_root'):
        audit+=['open Filter','open scoped Topology','example : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := '+ROOT]
    audit+=['#print axioms '+n for n in names]
    for edge in spec['edges']:
        c,h=edge['caller'],edge['helper']
        audit+=['set_option maxHeartbeats 0 in','run_cmd do',f'  let deps ← liftCoreM (`{c}).transitivelyUsedConstants',f'  unless deps.contains `{h} do throwError "EXPECTED_NATIVE_DEPENDENCY_MISSING={c}|{h}"',f'  IO.println "EXPECTED_NATIVE_DEPENDENCY_FOUND={c}|{h}"']
    audit+=trace_lines(spec)
    src=ev/'StageAudit.lean';src.write_text('\n'.join(audit)+'\n')
    output=invoke([src],'named-audit');verify_audits(output,names)
    need('SCOPED_EXCHANGE_TRACE=PASS' in output,'missing proof-graph gate')
    for edge in spec['edges']:
        need('EXPECTED_NATIVE_DEPENDENCY_FOUND='+edge['caller']+'|'+edge['helper'] in output,'missing positive trace')
    (ev/'compiler-context.json').write_text(json.dumps(dict(version=version,compiler_sha256=context[0],mathlib=MATHLIB,mathlib_witness=context[-1],cache_trust='hosted Actions/cache and pinned upstream Mathlib cache',modules=state),indent=2))
    return dict(fresh_builds=built,cache_hits=reused,audited=names,root_audited=ROOT in names,dependencies_traced=spec['edges'])

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--base',required=True);p.add_argument('--spec',required=True,type=Path);p.add_argument('--catalog',required=True,type=Path);p.add_argument('--source-only',action='store_true');p.add_argument('--objects',type=Path,default=Path('.serial-objects'));p.add_argument('--evidence',required=True,type=Path)
    a=p.parse_args();r=a.repo.resolve()
    base=git(r,'rev-parse','--verify',a.base+'^{commit}').decode().strip();head=git(r,'rev-parse','HEAD').decode().strip()
    a.evidence.mkdir(parents=True,exist_ok=False);ev=a.evidence.resolve()
    spec=json.loads(a.spec.read_text());catalog=json.loads(a.catalog.read_text());summary=dict(stage=spec['id'],target=spec['target'],base=base,head=head)
    try:
        plan=read_plan(r/PKG);summary['direct_source_counts']=verify_sources(r,base,spec,catalog,plan)
        if not a.source_only:summary.update(external(r,ev,a.objects.resolve(),spec,plan))
        result='SOURCE_CHECK_PASS' if a.source_only else 'STAGE_BUILD_AND_NAMED_AUDIT_PASS'
    except Exception as e:
        (ev/'result.txt').write_text('RESULT=FAIL\nERROR='+str(e)+'\n');raise
    (ev/'summary.json').write_text(json.dumps(summary,indent=2));(ev/'result.txt').write_text(f'RESULT={result}\nHEAD={head}\n')
    print(f'RESULT={result} HEAD={head}')
if __name__=='__main__': main()
