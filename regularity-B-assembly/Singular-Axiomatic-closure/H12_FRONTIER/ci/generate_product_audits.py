#!/usr/bin/env python3
"""Generate explicit exact-type/axiom audits for sixteen frozen adapter checkpoints.

Source processing only. No Lean invocation and no evidence promotion.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'SingularClosure.H12Frontier.'
GROUPS = [
    ('P01', 'ProductConstants', ['PRODUCT_CERTIFICATE']),
    ('P02', 'ProductConstants', ['product_literatureK2_eq', 'PRODUCT_CONSTANT_IDENTITY']),
    ('P03', 'ProductNormalization', ['product_coefficient_normalization', 'PRODUCT_COEFFICIENT_NORM_IDENTITY']),
    ('P04', 'ProductNormalization', ['PRODUCT_SMALLNESS_IFF', 'product_scale_cube_gt_one', 'PRODUCT_RADIUS_RATIO']),
    ('P05', 'ProductConstants', ['productDissipationConstant_eq', 'productDerivativeConstant_eq', 'PRODUCT_MARGIN_AND_BUDGETS']),
    ('P06', 'ProductMilestones', ['PRODUCT_GALERKIN_DIFFERENTIAL_INEQUALITY']),
    ('P07', 'ProductMilestones', ['PRODUCT_GALERKIN_ENERGY_INVARIANT', 'PRODUCT_GALERKIN_DISSIPATION_BUDGET', 'PRODUCT_GALERKIN_STATE_NORM_BOUND', 'PRODUCT_GALERKIN_STATE_THREE_INTEGRAL']),
    ('P08', 'ProductMilestones', ['PRODUCT_GALERKIN_SHARP_QUARTIC', 'PRODUCT_GALERKIN_SQUARE_BUDGET']),
    ('P09', 'ProductMilestones', ['PRODUCT_SIX_CHANNEL_BUDGET', 'PRODUCT_DATUM_AX6']),
    ('P10', 'ProductMilestones', ['PRODUCT_TIME_DERIVATIVE_POINTWISE', 'PRODUCT_TIME_DERIVATIVE_SQUARE', 'PRODUCT_TIME_DERIVATIVE_BUDGET']),
    ('P11', 'ProductMilestones', ['PRODUCT_GLOBAL_COMPACTNESS', 'PRODUCT_POSITIVE_ENSTROPHY', 'PRODUCT_POSITIVE_H2', 'PRODUCT_POSITIVE_ALL_ORDERS', 'PRODUCT_POSITIVE_FLOW']),
    ('P12', 'ProductMilestones', ['PRODUCT_LIMIT_NEGATIVE_HALF', 'PRODUCT_LIMIT_QUARTIC', 'PRODUCT_PHYSICAL_NEGATIVE_HALF', 'PRODUCT_PHYSICAL_QUARTIC', 'PRODUCT_QUANTITATIVE_REGULARITY']),
    ('P13', 'ProductMilestones', ['PRODUCT_GLOBAL_ENERGY_CLASS']),
    ('P14', 'ProductMilestones', ['PRODUCT_SERRIN_LERAYHOPF']),
    ('P15', 'ProductRoot', ['FRONTIER_H12_PRODUCT_NATIVE']),
    ('P16', 'ProductRoot', ['FRONTIER_H12_PRODUCT', 'FRONTIER_H12_PRODUCT_ADAPTER_CHAIN']),
]

def exact_type(source: str, name: str) -> str:
    m = re.search(r'^theorem ' + re.escape(name) + r'\b', source, re.M)
    if not m:
        raise ValueError('missing theorem: ' + name)
    header = source[m.end():].split(':=', 1)[0].strip()
    depth = 0
    for i, char in enumerate(header):
        if char in '([{': depth += 1
        elif char in ')]}': depth -= 1
        elif char == ':' and depth == 0:
            binders, target = header[:i].strip(), header[i+1:].strip()
            return ('∀ ' + binders + ',\n    ' + target) if binders else target
    raise ValueError('missing type separator: ' + name)

def main() -> None:
    entries = []
    declarations = []
    outdir = ROOT / 'ci/product_audits'
    outdir.mkdir(parents=True, exist_ok=True)
    for ident, module, names in GROUPS:
        source = (ROOT / 'SingularClosure/H12Frontier' / (module+'.lean')).read_text()
        code = f'import {PREFIX}{module}\n\n'
        code += '''set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

'''
        spec = {'schema_version':1, 'standard_axioms':['propext','Classical.choice','Quot.sound'], 'declarations':[]}
        for name in names:
            qualified = PREFIX+name
            code += 'example :\n    '+exact_type(source,name)+' :=\n  @'+qualified+'\n\n'
            code += '#eval IO.println "EXACT_TYPE_PASS:'+qualified+'"\n'
            code += '#print axioms '+qualified+'\n\n'
            spec['declarations'].append({'name':qualified, 'additional_allowed_axioms':[], 'required_axioms':[], 'exact_type_marker':'EXACT_TYPE_PASS:'+qualified})
            declarations.append(qualified)
        code += 'end\nend SingularClosure.H12Frontier\n'
        (outdir/(ident+'.lean')).write_text(code)
        (outdir/(ident+'.json')).write_text(json.dumps(spec,indent=2)+'\n')
        entries.append({'id':ident,'module':PREFIX+module,'audit':'ci/product_audits/'+ident+'.lean','spec':'ci/product_audits/'+ident+'.json','declarations':[PREFIX+n for n in names]})
    plan = {'schema_version':1,'source_base':'59a220c10f4f1600498c1b423b809695fb58a92f','expected_checkpoints':16,'entries':entries,'additional_allowed_axioms':[],'checkpoint_marker':'<=>'}
    (ROOT/'ci/product_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    # Delivery entry point: the same exact checks and audits, with the root import.
    entry = 'import '+PREFIX+'ProductRoot\n\n'
    entry += 'set_option autoImplicit false\nset_option Elab.async false\n\n'
    entry += '\n'.join('#check '+n for n in declarations)+'\n\n'
    entry += '#print axioms '+PREFIX+'FRONTIER_H12_PRODUCT_NATIVE\n'
    entry += '#print axioms '+PREFIX+'FRONTIER_H12_PRODUCT\n'
    entry += '#print axioms '+PREFIX+'FRONTIER_H12_PRODUCT_ADAPTER_CHAIN\n'
    (ROOT/'FRONTIER_H12_PRODUCT_ADAPTER_CHAIN.lean').write_text(entry)
    outputs = [ROOT/'SingularClosure/H12Frontier'/ (m+'.lean') for m in sorted({x[1] for x in GROUPS})]
    outputs += sorted(outdir.glob('*'))+[ROOT/'ci/product_plan.json', ROOT/'FRONTIER_H12_PRODUCT_ADAPTER_CHAIN.lean']
    manifest={'schema_version':1,'generated_by':'ci/generate_product_audits.py','files':[{'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in outputs]}
    (ROOT/'ci/product_source_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'checkpoints':len(entries),'declarations':len(declarations),'local_lean_executions':0}))

if __name__ == '__main__':
    main()
