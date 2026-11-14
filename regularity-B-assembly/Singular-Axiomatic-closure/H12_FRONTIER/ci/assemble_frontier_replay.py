#!/usr/bin/env python3
"""Hash-locked coefficient-parametric replay; no compiler invocation.
Only the new namespace is generated. The fixed frontier coefficient is a
separate concrete obligation, not inferred from the parametric proofs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def extract_declaration(text: str, name: str) -> str:
    m = re.search(r"^((?:theorem|def) " + re.escape(name) + r")\b", text, re.M)
    if m is None:
        raise ValueError(f"missing declaration: {name}")
    tail = text[m.end():]
    end = re.search(r"^((?:theorem|def|structure) |end(?: |$))", tail, re.M)
    body = text[m.start():m.end() + (end.start() if end else len(tail))]
    while (doc := re.search(r"/--(?:(?!/--)[\s\S])*?-/\s*$", body)) is not None:
        body = body[:doc.start()].rstrip() + "\n"
    if ":=" not in body:
        raise ValueError(f"missing proof body: {name}")
    return body.strip() + "\n"


def transform(body: str, original: str, names: dict[str, str]) -> str:
    kind = "def" if body.startswith("def ") else "theorem"
    head = f"{kind} {original}"
    if not body.startswith(head):
        raise ValueError("unexpected declaration header")
    body = "@@HEAD@@" + body[len(head):]
    body = body.replace("g.critical_differential_inequality", "(differentialInequality cert g)")
    body = body.replace("criticalNonlinearConstant_bound", "cert.bound")
    body = body.replace("criticalNonlinearConstant_pos", "cert.positive")
    body = re.sub(r"\bcriticalNonlinearConstant\b", "cert.constant", body)
    for old, new in sorted(names.items(), key=lambda pair: -len(pair[0])):
        if old.startswith("GalerkinSolution."):
            continue
        body = re.sub(r"(?<![\w.])" + re.escape(old) + r"(?![\w])", f"({new} cert)", body)
    return body.replace("@@HEAD@@", f"{kind} {names[original]} (cert : NonlinearCertificate)")


def exact_audit(module: str, text: str) -> tuple[str, list[str]]:
    audit = f"import SingularClosure.H12Frontier.{module}\n" + """set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

"""
    declarations: list[str] = []
    for m in re.finditer(r"^theorem ([\w.]+)([\s\S]*?)(?=\n(?:theorem|def|end)(?:\s|$)|\Z)", text, re.M):
        name, signature = m.group(1), m.group(2).split(":=", 1)[0].strip()
        depth, split = 0, None
        for i, char in enumerate(signature):
            if char in "({[":
                depth += 1
            elif char in ")}]":
                depth -= 1
            elif char == ":" and depth == 0:
                split = i
                break
        if split is None:
            raise ValueError(f"unparsed exact type: {name}")
        binders, goal = signature[:split].strip(), signature[split + 1:].strip()
        qualified = "SingularClosure.H12Frontier.Replay." + name
        audit += f"example : ∀ {binders},\n    {goal} :=\n  @{qualified}\n\n"
        audit += f'#eval IO.println "EXACT_TYPE_PASS:{qualified}"\n#print axioms {qualified}\n\n'
        declarations.append(qualified)
    if not declarations:
        raise ValueError(f"empty audit: {module}")
    return audit + "end\nend SingularClosure.H12Frontier.Replay\n", declarations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-existing", action="store_true")
    args = parser.parse_args()
    spec = json.loads((ROOT / "ci/frontier_replay_spec.json").read_text(encoding="utf-8"))
    inputs: dict[str, str] = {}
    for relative, expected in spec["source_sha256"].items():
        source = ROOT / relative
        if hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise ValueError(f"base source mismatch: {relative}")
        inputs[relative] = source.read_text(encoding="utf-8")
    names = {d["source_declaration"]: d["target_declaration"]
             for module in spec["modules"] for d in module["declarations"]}
    outputs: dict[str, str] = {}
    plan = json.loads((ROOT / "ci/frontier_plan.json").read_text(encoding="utf-8"))
    plan["entries"] = [e for e in plan["entries"] if not e["id"].startswith("S_REPLAY_")
                       and not e["id"].startswith("SUPPORT_")]
    for module in spec["modules"]:
        header = "\n".join("import " + value for value in module["imports"]) + """

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

"""
        code = header + "\n".join(transform(extract_declaration(inputs[d["source_path"]],
                    d["source_declaration"]), d["source_declaration"], names)
                    for d in module["declarations"])
        code += "\nend\nend SingularClosure.H12Frontier.Replay\n"
        outputs[f"SingularClosure/H12Frontier/{module['module']}.lean"] = code
        audit, declarations = exact_audit(module["module"], code)
        ident = "S_REPLAY_" + module["module"].removeprefix("Replay").upper()
        audit_path, spec_path = f"ci/frontier_audits/{ident}.lean", f"ci/frontier_audits/{ident}.json"
        outputs[audit_path] = audit
        outputs[spec_path] = json.dumps({"schema_version": 1,
            "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "declarations": [{"name": n, "additional_allowed_axioms": [], "required_axioms": [],
                "exact_type_marker": "EXACT_TYPE_PASS:" + n} for n in declarations]}, indent=2) + "\n"
        plan["entries"].append({"id": ident,
            "module": "SingularClosure.H12Frontier." + module["module"],
            "audit": audit_path, "spec": spec_path,
            "role": "CERTIFICATE_PARAMETRIC_SUPPORT_NOT_CONCRETE_MILESTONE",
            "auxiliary_obligations": ["fixed frontier nonlinear certificate required for concrete specialization"]})
    outputs["ci/frontier_plan.json"] = json.dumps(plan, indent=2) + "\n"
    for relative, content in outputs.items():
        target = ROOT / relative
        if args.check_existing and target.exists() and target.read_text(encoding="utf-8") != content:
            raise ValueError(f"tracked generated source mismatch: {relative}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8", newline="\n")
    manifest = {"generator": "ci/assemble_frontier_replay.py", "source_sha256": spec["source_sha256"],
        "concrete_milestones_promoted": [], "generated": []}
    for relative, content in outputs.items():
        raw = content.encode("utf-8")
        manifest["generated"].append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest(),
            "git_blob_sha": hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()})
    evidence = ROOT / "evidence/frontier"
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / "generated-source-manifest.json").write_text(json.dumps(manifest, indent=2)+"\n", encoding="utf-8")
    with zipfile.ZipFile(ROOT / "evidence/assembled_source_snapshot.zip", "w", zipfile.ZIP_DEFLATED) as archive:
        for source in sorted(ROOT.rglob("*")):
            rel = source.relative_to(ROOT)
            if source.is_file() and not any(p in {".lake", "evidence", "__pycache__"} for p in rel.parts):
                archive.write(source, str(rel))
    print(f"GENERATED_FRONTIER_SUPPORT_FILES={len(outputs)}")
    print("CONCRETE_MILESTONES_PROMOTED=0")


if __name__ == "__main__":
    main()
