#!/usr/bin/env python3
"""Specialize the compiled replay to the proved concrete frontier coefficient.
No Lean invocation, no branch updates, no status promotion by generation.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "SingularClosure.H12Frontier."
FOLDER = ROOT / "SingularClosure/H12Frontier"


def header(module: str, declaration: str) -> str:
    source = (FOLDER / (module + ".lean")).read_text(encoding="utf-8")
    m = re.search(r"^theorem " + re.escape(declaration) + r"\b", source, re.M)
    if not m:
        raise ValueError("missing declaration " + declaration)
    return source[m.end():].split(":=", 1)[0].strip()


def split_header(signature: str) -> tuple[str, str]:
    depth = 0
    for i, char in enumerate(signature):
        if char in "([{": depth += 1
        elif char in ")]}": depth -= 1
        elif char == ":" and depth == 0:
            return signature[:i].strip(), signature[i + 1:].strip()
    raise ValueError("no top-level type separator")


def full_type(signature: str) -> str:
    binders, target = split_header(signature)
    return ("∀ " + binders + ",\n    " + target) if binders else target


def specialize(signature: str) -> str:
    signature = signature.replace("(cert : NonlinearCertificate)", "", 1).strip()
    signature = signature.replace("cert.constant", "frontierConstant")
    signature = signature.replace("(dissipationConstant cert)", "frontierDissipationConstant")
    signature = signature.replace("(derivativeConstant cert)", "frontierDerivativeConstant")
    return full_type(signature)


def preamble(imports: list[str]) -> str:
    return "\n".join("import " + name for name in imports) + """

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

"""


def main() -> None:
    outputs: dict[str, str] = {}
    endpoints: dict[str, tuple[str, str, str]] = {}
    group = [
        ("FiniteMilestones", "ReplayEnergy", [
            ("E04", "energyInvariant", "frontierGalerkinEnergyInvariant"),
            ("E05", "dissipationBudget", "frontierDissipationBudget")]),
        ("DerivativeMilestone", "ReplayDerivative", [
            ("E07", "timeDerivativeBudget", "frontierTimeDerivativeBudget")]),
        ("PositiveMilestones", "ReplayPositiveTime", [
            ("E08", "positiveEnstrophy", "frontierPositiveTimeEnstrophyAccumulation"),
            ("E09", "positiveH2", "frontierPositiveTimeH2Bound"),
            ("E10", "positiveAllOrders", "frontierPositiveTimeAllOrders")]),
        ("LimitMilestones", "ReplayLimit", [
            ("E11", "limitNegativeHalf", "frontierLimitNegativeHalf"),
            ("E12", "limitQuartic", "frontierLimitSharpQuartic")]),
        ("Root", "ReplayClosure", [
            ("E13", "fullClosure", "FRONTIER_H12_NATIVE")])]
    for module, source_module, declarations in group:
        code = preamble([PREFIX + "NonlinearBound", PREFIX + source_module])
        if module in {"LimitMilestones", "Root"}:
            code += """def frontierDissipationConstant (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  Replay.dissipationConstant frontierCertificate ν a

def frontierDerivativeConstant (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  Replay.derivativeConstant frontierCertificate ν a

""" if module == "LimitMilestones" else ""
            if module == "Root":
                code = code.replace("import " + PREFIX + "ReplayClosure",
                    "import " + PREFIX + "ReplayClosure\nimport " + PREFIX + "LimitMilestones")
        for ident, old, new in declarations:
            exact_type = specialize(header(source_module, old))
            code += f"theorem {new} :\n    {exact_type} :=\n  @Replay.{old} frontierCertificate\n\n"
            endpoints[ident] = (module, new, exact_type)
        if module == "FiniteMilestones":
            new = "frontierSharpQuarticBudget"
            exact_type = """∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) ^ 2 +
        4 * (ν - frontierConstant * ‖a‖) *
          (∫ s in (0 : ℝ)..t, criticalEnergy 2 N (g.coeff s) ^ 2) ≤
        criticalEnergy 1 N (g.coeff 0) ^ 2"""
            code += f"theorem {new} :\n    {exact_type} := by\n" + """  intro ν T N a hreal hsmall hT g
  exact CRITICAL_SQUARE_BUDGET hT frontierConstant_pos.le (norm_nonneg a) hsmall
    ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 2).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => Replay.differentialInequality frontierCertificate g ht.1)
    (fun t _ => criticalEnergy_interpolation N (g.coeff t))

"""
            endpoints["E06"] = (module, new, exact_type)
        if module == "Root":
            root_type = endpoints["E13"][2]
            if "(hsmall : frontierConstant * ‖a‖ < ν)" not in root_type:
                raise ValueError("registered root smallness binder not found")
            exact_type = root_type.replace("(hsmall : frontierConstant * ‖a‖ < ν)",
                "(hsmall : paperNorm 1 a < (Real.sqrt 2 / literatureK2) * ν)", 1)
            code += f"theorem FRONTIER_H12 :\n    {exact_type} := by\n" + """  intro ν hν a ha hsmall
  exact FRONTIER_H12_NATIVE ν hν a ha
    ((FRONTIER_H12_SMALLNESS_IFF ν a ha.mean_zero).mp hsmall)

"""
            endpoints["E14"] = (module, "FRONTIER_H12", exact_type)
        outputs[f"SingularClosure/H12Frontier/{module}.lean"] = code + "end\nend SingularClosure.H12Frontier\n"
    for ident, module, name in [
        ("E02", "ConstantNormalization", "FRONTIER_H12_CONSTANT_NORMALIZATION"),
        ("E03", "NonlinearBound", "FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND"),
        ("S_BUNDLE", "LiteratureConstants", "CONCRETE_LITERATURE_SOBOLEV_BUNDLE"),
        ("S_RADIUS", "ConstantNormalization", "literal_radius_strictly_enlarged")]:
        endpoints[ident] = (module, name, full_type(header(module, name)))
    plan = json.loads((ROOT / "ci/frontier_plan.json").read_text(encoding="utf-8"))
    plan["entries"] = [e for e in plan["entries"] if e["id"] not in endpoints]
    for ident in sorted(endpoints):
        module, name, exact_type = endpoints[ident]
        qualified = PREFIX + name
        audit = preamble([PREFIX + module]).replace("set_option Elab.async true", "set_option Elab.async false")
        audit += f"example :\n    {exact_type} :=\n  @{qualified}\n\n"
        audit += f'#eval IO.println "EXACT_TYPE_PASS:{qualified}"\n#print axioms {qualified}\n\n'
        audit += "end\nend SingularClosure.H12Frontier\n"
        audit_path, spec_path = f"ci/frontier_audits/{ident}.lean", f"ci/frontier_audits/{ident}.json"
        outputs[audit_path] = audit
        outputs[spec_path] = json.dumps({"schema_version": 1,
            "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "declarations": [{"name": qualified, "additional_allowed_axioms": [],
                "required_axioms": [], "exact_type_marker": "EXACT_TYPE_PASS:" + qualified}]}, indent=2)+"\n"
        plan["entries"].append({"id":ident,"module":PREFIX+module,"audit":audit_path,"spec":spec_path,
            "role":"CONCRETE_MILESTONE" if ident.startswith("E") else "CONCRETE_ANALYTIC_SUPPORT",
            "auxiliary_obligations":[],"scope_review_required":True})
    outputs["ci/frontier_plan.json"] = json.dumps(plan,indent=2)+"\n"
    manifest_path = ROOT / "evidence/frontier/generated-source-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["generated"] = [e for e in manifest["generated"] if e["path"] not in outputs]
    for relative, content in outputs.items():
        target = ROOT / relative
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(content,encoding="utf-8",newline="\n")
        data=content.encode("utf-8")
        manifest["generated"].append({"path":relative,"sha256":hashlib.sha256(data).hexdigest(),
            "git_blob_sha":hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()})
    manifest["concrete_generator"] = "ci/assemble_frontier_concrete.py"
    manifest["concrete_milestones_promoted"] = []
    manifest_path.write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    with zipfile.ZipFile(ROOT / "evidence/assembled_source_snapshot.zip","w",zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ROOT.rglob("*")):
            rel=p.relative_to(ROOT)
            if p.is_file() and not any(a in {".lake","evidence","__pycache__"} for a in rel.parts):
                z.write(p,str(rel))
    print(f"CONCRETE_CANDIDATE_ENDPOINTS={len(endpoints)}")
    print("CONCRETE_MILESTONES_PROMOTED=0")

if __name__=="__main__":
    main()
