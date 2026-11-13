#!/usr/bin/env python3
"""External-only cached build with independent, fresh theorem-level audits.

PASS_STANDARD_ONLY concerns the exact printed theorem type; it does not assert
that analytic premises of that type are discharged.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

TOOLCHAIN='leanprover/lean4:v4.34.0-rc1'
MATHLIB='de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11'
ALLOWED={'propext','Classical.choice','Quot.sound'}
RECORD=re.compile(r"['‘]([^'’\r\n]+)['’]\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",re.M)
ANSI=re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def strip_comments(text):
    result=[]; i=0; depth=0; string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; i+=2
            elif text.startswith('-/',i): depth-=1; i+=2
            else: result.append('\n' if text[i]=='\n' else ' '); i+=1
        elif string:
            if text[i]=='\\': result.extend('  '); i+=2
            elif text[i]=='"': string=False; result.append(' '); i+=1
            else: result.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text.startswith('/-',i): depth=1; result.extend('  '); i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i); end=len(text) if end<0 else end
            result.extend(' '*(end-i)); i=end
        elif text[i]=='"': string=True; result.append(' '); i+=1
        else: result.append(text[i]); i+=1
    return ''.join(result)

def declarations(text):
    stack=[]; names=[]
    for line in strip_comments(text).splitlines():
        s=line.strip()
        ns=re.match(r'^namespace\s+([^\s]+)',s)
        section=re.match(r'^(?:noncomputable\s+)?section(?:\s+[^\s]+)?$',s)
        end=re.match(r'^end(?:\s+[^\s]+)?$',s)
        if ns: stack.append(('namespace',ns.group(1))); continue
        if section: stack.append(('section','')); continue
        if end:
            if stack: stack.pop()
            continue
        match=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:(private|protected)\s+)?(?:noncomputable\s+)?(?:theorem|lemma|opaque)\s+([^\s(:{]+)',s)
        if match and match.group(1)!='private':
            name=match.group(2)
            prefix='.'.join(v for k,v in stack if k=='namespace')
            names.append(name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(x for x in (prefix,name) if x))
    if len(names)!=len(set(names)): raise ValueError('Duplicate audit names')
    return names

def verify_axioms(log,names):
    parsed={}
    for m in RECORD.finditer(ANSI.sub('',log)):
        raw=(m.group(2) or '').strip()
        # Approved foundational names have no universe instantiations.
        values=set(x.strip() for x in raw.split(',') if x.strip())
        if m.group(1) in parsed: raise ValueError('Duplicate axiom record: '+m.group(1))
        parsed[m.group(1)]=values
    if set(parsed)!=set(names): raise ValueError('Missing or unexpected axiom records')
    bad={k:sorted(v-ALLOWED) for k,v in parsed.items() if v-ALLOWED}
    if bad: raise ValueError('Unapproved axioms: '+str(bad))
    return [{'name':n,'axioms':sorted(parsed[n]),'status':'PASS_STANDARD_ONLY'} for n in names]

def run(command,package,log):
    log.parent.mkdir(exist_ok=True,parents=True)
    started=time.monotonic()
    with log.open('w',encoding='utf-8') as out:
        proc=subprocess.Popen(command,cwd=package,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
        for line in proc.stdout:
            out.write(line); out.flush(); print(line,end='',flush=True)
        code=proc.wait()
    return code,round(time.monotonic()-started,3)

def modules(package):
    found={}
    roots=[(package,'FourierHodgeLaws'),(package,'FourierHodgeLaws_inhabitant'),
           (package,'NSEMaxwell'),(package,'MethlibEndpoints'),
           (package/'LocalDependencies/Maxwell','MaxwellEndpoint'),
           (package/'LocalDependencies/Forward','NSEMaxwellForward'),
           (package/'LocalDependencies/Reverse','NSEMaxwellReverse'),
           (package/'NativeSources/methlib','SingularClosure')]
    for root,prefix in roots:
        paths=[root/(prefix+'.lean')]+sorted((root/prefix).rglob('*.lean'))
        for path in paths:
            if path.is_file(): found[path.relative_to(root).with_suffix('').as_posix().replace('/','.')]=path
    new={k for k in found if k.startswith('FourierHodgeLaws.') or k in ('FourierHodgeLaws','FourierHodgeLaws_inhabitant')}
    visited=set(); active=set(); order=[]
    def visit(name):
        if name in visited:return
        if name in active:raise ValueError('Import cycle '+name)
        active.add(name)
        text=strip_comments(found[name].read_text())
        for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)',text,re.M):
            for dep in match.group(1).split():
                if dep in found: visit(dep)
        active.remove(name); visited.add(name); order.append(name)
    for name in sorted(new): visit(name)
    return found,new,order

def source_manifest(package):
    wanted=[]
    for path in sorted(package.rglob('*')):
        if not path.is_file():continue
        rel=path.relative_to(package)
        if any(p in ('.lake','hodge-evidence','__pycache__') for p in rel.parts):continue
        wanted.append({'path':rel.as_posix(),'sha256':digest(path),'bytes':path.stat().st_size})
    return wanted

def main():
    p=argparse.ArgumentParser(); p.add_argument('--package',type=Path,required=True)
    p.add_argument('--phase',choices=['dependencies','build','all'],default='all')
    a=p.parse_args(); package=a.package.resolve(); evidence=package/'hodge-evidence'; evidence.mkdir(exist_ok=True)
    os.environ['ELAN_TOOLCHAIN']=TOOLCHAIN; os.environ['MATHLIB_NO_CACHE_ON_UPDATE']='1'
    if a.phase in ('dependencies','all'):
        code,_=run(['lean','--version'],package,evidence/'lean-version.log')
        version=(evidence/'lean-version.log').read_text().strip()
        if code or not re.search(r'version 4\.34\.0-rc1,',version):raise ValueError('Compiler mismatch')
        lockhash=digest(package/'lake-manifest.json')
        lock=json.loads((package/'lake-manifest.json').read_text())
        if next(v['rev'] for v in lock['packages'] if v['name']=='mathlib')!=MATHLIB:raise ValueError('Mathlib pin mismatch')
        for command,log in [([sys.executable,'scripts/hydrate_native_sources.py','--package-root',str(package),'--dependency-root',str(package/'.lake/packages'),'--report',str(evidence/'hydration.json')],'hydration.log'),
                            ([sys.executable,'scripts/verify_native_sources.py','--package-root',str(package),'--dependency-root',str(package/'.lake/packages'),'--report',str(evidence/'native-sources.json')],'native-sources.log'),
                            (['lake','exe','cache','get','Mathlib'],'mathlib-cache.log')]:
            code,_=run(command,package,evidence/log)
            if code:raise ValueError('Dependency phase failed: '+log)
        if digest(package/'lake-manifest.json')!=lockhash:raise ValueError('Lockfile changed')
        revisions=[]
        for item in lock['packages']:
            path=package/'.lake/packages'/item['name']
            revision=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
            status=subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True)
            if revision!=item['rev'] or status:raise ValueError('Dependency mismatch: '+item['name'])
            revisions.append({'name':item['name'],'revision':revision})
        if not (package/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').is_file():raise ValueError('Missing official Mathlib object')
        (evidence/'provenance.json').write_text(json.dumps({'requested_toolchain':TOOLCHAIN,'actual_lean_version':version,'dependencies':revisions,'source_commit':os.environ.get('GITHUB_SHA'),'lockfile_sha256':lockhash,'platform':sys.platform},indent=2)+'\n')
    if a.phase not in ('build','all'):return 0
    before=source_manifest(package); (evidence/'source-manifest.json').write_text(json.dumps({'files':before},indent=2)+'\n')
    found,new,order=modules(package)
    if not new:raise ValueError('No new proof modules')
    for name in new:
        code=strip_comments(found[name].read_text())
        if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',code):raise ValueError('Forbidden proof admission in '+name)
    results=[]; failure=False
    for name in order:
        slug=name.replace('.','-'); is_new=name in new
        code,seconds=run(['lake','build',name],package,evidence/(slug+'-build.log'))
        result={'module':name,'source_sha256':digest(found[name]),'new_module':is_new,'build_exit':code,'seconds':seconds}
        if code:
            result['status']='BUILD_FAILED'; failure=True
        elif not is_new:
            result['status']='UPSTREAM_BUILD_PASS'
        else:
            names=declarations(found[name].read_text())
            audit=evidence/(slug+'-Audit.lean')
            audit.write_text('import '+name+'\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.width 180\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
            code,_=run(['lake','env','lean',str(audit)],package,evidence/(slug+'-audit.log'))
            result['audit_exit']=code; result['audit_source_sha256']=digest(audit)
            try:
                if code:raise ValueError('Audit elaboration failed')
                result['declarations']=verify_axioms((evidence/(slug+'-audit.log')).read_text(),names)
                result['status']='PASS_STANDARD_ONLY' if names else 'BUILD_PASS_NO_NAMED_THEOREMS'
            except ValueError as exc:
                result['status']='AUDIT_FAILED'; result['error']=str(exc); failure=True
            (evidence/(slug+'-result.json')).write_text(json.dumps(result,indent=2)+'\n')
        results.append(result)
        (evidence/'summary.json').write_text(json.dumps({'status':'IN_PROGRESS','results':results,'unconditional_promotion':'REQUIRES_EXACT_TYPE_REVIEW'},indent=2)+'\n')
    if source_manifest(package)!=before:raise ValueError('Build changed source files')
    summary={'status':'FAIL' if failure else 'PASS','results':results,'unconditional_promotion':'REQUIRES_EXACT_TYPE_REVIEW','source_manifest_sha256':digest(evidence/'source-manifest.json')}
    (evidence/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':summary['status'],'new_modules':len(new),'built_modules':len(results)}))
    return 1 if failure else 0

if __name__=='__main__':
    try:sys.exit(main())
    except Exception as exc:
        print(type(exc).__name__+': '+str(exc),file=sys.stderr);sys.exit(1)
