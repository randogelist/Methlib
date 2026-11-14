from __future__ import annotations
import argparse, hashlib, json, re, subprocess
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAMES = [
 "QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData",
 "QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs",
 "QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs",
 "QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton",
 "QFA.CorrectedPhysicalRoot.selectedTail_smooth",
 "QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion",
 "QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED",
]
SOURCES = ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "QFACorrectedRoot.lean",
           "QFACorrectedRoot/Analytic.lean", "QFACorrectedRoot/PhysicalRoot.lean",
           "Audit.lean", "scripts/audit.py"]

def clean_lean(text: str) -> str:
    out=[]; i=0; depth=0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif depth:
            if text[i]=='\n': out.append('\n')
            i += 1
        elif text.startswith('--', i):
            j=text.find('\n',i); i=len(text) if j<0 else j
        elif text[i]=='"':
            out.append('""'); i+=1
            while i<len(text):
                if text[i]=='\\': i+=2
                elif text[i]=='"': i+=1; break
                else: i+=1
        else: out.append(text[i]); i+=1
    if depth: raise RuntimeError('UNTERMINATED_COMMENT')
    return ''.join(out)

def static(base: Path) -> dict:
    for rel in SOURCES:
        if not (base/rel).is_file(): raise RuntimeError(f'MISSING_SOURCE:{rel}')
    for rel in [x for x in SOURCES if x.endswith('.lean')]:
        code=clean_lean((base/rel).read_text(encoding='utf-8'))
        if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', code):
            raise RuntimeError(f'UNAPPROVED_PROOF_CONSTRUCTION:{rel}')
    if (base/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.0':
        raise RuntimeError('TOOLCHAIN_MISMATCH')
    return {rel: hashlib.sha256((base/rel).read_bytes()).hexdigest() for rel in SOURCES}

def run(base: Path, args: list[str], log: Path) -> str:
    p=subprocess.run(args,cwd=base,text=True,encoding='utf-8',errors='replace',
                     stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_text(p.stdout,encoding='utf-8')
    print(p.stdout,end='')
    if p.returncode: raise RuntimeError(f'COMMAND_FAILED:{args}:{p.returncode}')
    return p.stdout

def parse(log: str) -> dict:
    if 'sorryAx' in log or re.search(r'error(?:\([^\n)]*\))?:',log):
        raise RuntimeError('LEAN_ERROR_OR_SORRY')
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log))
    for name in re.findall(r"'([^']+)' does not depend on any axioms",log): reports[name]=''
    if set(reports) != set(NAMES): raise RuntimeError('DECLARATION_AUDIT_MISMATCH')
    out={}
    for name,raw in reports.items():
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        if not axioms <= ALLOWED: raise RuntimeError(f'UNAPPROVED_AXIOMS:{name}:{axioms-ALLOWED}')
        b=f'TYPE_BEGIN:{name}\n'; e=f'TYPE_END:{name}\n'
        if log.count(b)!=1 or log.count(e)!=1: raise RuntimeError(f'TYPE_MARKER_MISMATCH:{name}')
        typ=log.split(b,1)[1].split(e,1)[0].strip()
        if not typ: raise RuntimeError(f'EMPTY_TYPE:{name}')
        out[name]={'type':typ,'axioms':sorted(axioms)}
    return out

def main() -> int:
    ap=argparse.ArgumentParser(); ap.add_argument('--static',action='store_true'); ap.add_argument('--external',action='store_true')
    ns=ap.parse_args(); base=Path(__file__).resolve().parents[1]
    hashes=static(base)
    if ns.static:
        print(json.dumps({'static':'PASS','sources':hashes,'local_lean_executions':0},indent=2)); return 0
    if not ns.external: raise RuntimeError('MODE_REQUIRED')
    ev=base/'evidence'; ev.mkdir(exist_ok=True)
    status={'status':'PENDING','formal_closure':False,'conditional_formal_closure':False,
            'physical_QFA_root_inferred':False,'sources':hashes}
    try:
        ver=run(base,['lake','env','lean','--version'],ev/'lean-version.txt')
        if not re.search(r'version 4\.33\.0,',ver): raise RuntimeError('COMPILER_VERSION_MISMATCH')
        run(base,['lake','update'],ev/'lake-update.log')
        run(base,['lake','exe','cache','get'],ev/'mathlib-cache.log')
        run(base,['lake','build','QFACorrectedRoot'],ev/'build.log')
        log=run(base,['lake','env','lean','Audit.lean'],ev/'axioms.log')
        status['declarations']=parse(log); status['status']='PASS'
        status['formal_closure']=True; status['conditional_formal_closure']=True
        status['physical_QFA_root_inferred']=True
        print('QFA_CORRECTED_CONDITIONAL_FORMAL_CLOSURE_PASS')
    except Exception as e:
        status['status']='FAIL'; status['error']=str(e); raise
    finally:
        (ev/'status.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
    return 0

if __name__=='__main__': raise SystemExit(main())
