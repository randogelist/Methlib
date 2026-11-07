#!/usr/bin/env python3
"""Prepare exact rational coordinates for external native Lean proof admission."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PACKAGE_ROOT = Path(__file__).resolve().parent.parent

def natural(x, name):
    if type(x) is not int or x < 0:
        raise ValueError(name + " must be a nonnegative integer")
    return x

def rational(x, name):
    if not isinstance(x, list) or len(x) != 2:
        raise ValueError(name + " must be [integer numerator, positive denominator]")
    a, b = x
    if type(a) is not int or type(b) is not int or b <= 0:
        raise ValueError(name + " has invalid integer/denominator")
    return Fraction(a, b)

def validate(raw):
    if not isinstance(raw, dict):
        raise ValueError("candidate must be an object")
    required = {"schema", "mode", "index", "coefficient", "centers", "radii"}
    allowed = required | {"tail_cutoff"}
    if set(raw) - allowed or not required <= set(raw):
        raise ValueError("unexpected or missing candidate fields")
    if type(raw["schema"]) is not int or raw["schema"] != 1:
        raise ValueError("schema must be 1")
    mode = raw["mode"]
    if mode not in ("sign_row", "margin_step"):
        raise ValueError("mode must be sign_row or margin_step")
    index = natural(raw["index"], "index")
    coefficient = natural(raw["coefficient"], "coefficient")
    degree = index if mode == "sign_row" else index + 1
    cutoff = natural(raw.get("tail_cutoff", degree), "tail_cutoff")
    cs, es = raw["centers"], raw["radii"]
    if not isinstance(cs, list) or not isinstance(es, list):
        raise ValueError("centers and radii must be lists")
    if len(cs) != degree + 1 or len(es) != degree + 1:
        raise ValueError("coordinate lengths must equal required degree + 1")
    centers = [rational(x, "center") for x in cs]
    radii = [rational(x, "radius") for x in es]
    if any(e < 0 for e in radii):
        raise ValueError("radii must be nonnegative")
    canonical = {
        "schema": 1, "mode": mode, "index": index,
        "coefficient": coefficient, "tail_cutoff": cutoff,
        "centers": [[x.numerator, x.denominator] for x in centers],
        "radii": [[x.numerator, x.denominator] for x in radii],
    }
    return canonical, degree

def rat_text(pair):
    a, b = pair
    return f"(({a} : ℚ) / ({b} : ℚ))"

def data_source(c, degree):
    centers = ", ".join(map(rat_text, c["centers"]))
    radii = ", ".join(map(rat_text, c["radii"]))
    return f"""import Tail16Frontier.MomentData

set_option autoImplicit false
namespace SubmissionData
def index : Nat := {c["index"]}
def coefficient : Nat := {c["coefficient"]}
def degree : Nat := {degree}
def tailCutoff : Nat := {c["tail_cutoff"]}
def moments : Tail16Frontier.MomentData :=
  {{ centers := [{centers}], radii := [{radii}] }}
theorem shape : moments.shapeCheck degree = true := by decide
end SubmissionData
"""

def admission_source(c, with_tail):
    imports = "import SubmissionEvidence\nimport Tail16Frontier.CheckedAdmission\n"
    if with_tail:
        imports += "import SubmissionTail\n"
    s = imports + """
set_option autoImplicit false
namespace SubmissionAdmission
open Tail16Frontier

theorem actualMoments :
    SubmissionData.moments.Encloses SubmissionData.degree :=
  SubmissionEvidence.encloses
"""
    names = ["SubmissionAdmission.actualMoments"]
    if c["mode"] == "sign_row":
        s += """
theorem arithmeticAccepted :
    signCheck SubmissionData.moments SubmissionData.index = true := by
  norm_num [signCheck, allBelow, MomentData.shapeCheck, qBernstein, entryError,
    MomentData.center, MomentData.radius, rationalAt,
    SubmissionData.moments, SubmissionData.index,
    Finset.sum_range_succ, Nat.choose]

theorem actualRow :
    ∀ j : Nat, j ≤ SubmissionData.index →
      0 ≤ RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment SubmissionData.index j := by
  exact signCheck_sound SubmissionData.moments SubmissionData.index
    actualMoments arithmeticAccepted

theorem finiteCancellation :
    ∀ n : Nat, n < SubmissionData.index →
      RH_HilbertLimit.rowCancellation
        RH_HilbertLimit.actualNormalizedMoment n = 0 := by
  exact cancellation_eq_zero_of_nonnegative_row SubmissionData.index actualRow

theorem finitePrefix : Prefix SubmissionData.coefficient SubmissionData.index := by
  exact prefix_of_nonnegative_row SubmissionData.coefficient
    SubmissionData.index actualRow
"""
        names += ["SubmissionAdmission.arithmeticAccepted", "SubmissionAdmission.actualRow",
                  "SubmissionAdmission.finiteCancellation", "SubmissionAdmission.finitePrefix"]
    else:
        s += """
theorem arithmeticAccepted :
    marginCheck SubmissionData.moments SubmissionData.index
      SubmissionData.coefficient = true := by
  norm_num [marginCheck, MomentData.shapeCheck, qGap, qGapError,
    qVariation, rowError, qBernstein, entryError,
    MomentData.center, MomentData.radius, rationalAt,
    SubmissionData.moments, SubmissionData.index, SubmissionData.coefficient,
    Finset.sum_range_succ, Nat.choose]

theorem actualStep : BudgetStep SubmissionData.coefficient SubmissionData.index := by
  exact marginCheck_sound SubmissionData.moments SubmissionData.index
    SubmissionData.coefficient actualMoments arithmeticAccepted
"""
        names += ["SubmissionAdmission.arithmeticAccepted", "SubmissionAdmission.actualStep"]
    if with_tail:
        s += """
theorem checkedTail :
    Tail SubmissionData.coefficient SubmissionData.tailCutoff :=
  SubmissionTail.tail

theorem admittedRH : _root_.RiemannHypothesis := by
  exact tail_nativeRH SubmissionData.coefficient
    SubmissionData.tailCutoff checkedTail
"""
        names += ["SubmissionAdmission.checkedTail", "SubmissionAdmission.admittedRH"]
    s += "\nend SubmissionAdmission\n"
    return s, names

def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()

def prepare(candidate, moment_proof, tail_proof=None):
    raw = json.loads(candidate.read_text(encoding="utf-8-sig"))
    canonical, degree = validate(raw)
    canonical_bytes = (json.dumps(canonical, sort_keys=True, separators=(",", ":")) + "\n").encode()
    proof_bytes = moment_proof.read_bytes()
    tail_bytes = tail_proof.read_bytes() if tail_proof is not None else b""
    identity = digest_bytes(canonical_bytes + b"\x00" + proof_bytes + b"\x00" + tail_bytes)
    out = PACKAGE_ROOT / "_submission" / identity[:20]
    out.mkdir(parents=True, exist_ok=True)
    (out / "canonical.json").write_bytes(canonical_bytes)
    (out / "SubmissionData.lean").write_text(data_source(canonical, degree), encoding="utf-8")
    # The proof file must define a CLOSED theorem SubmissionEvidence.encloses.
    # It is compiler input, never executed by Python and never accepted by a text scan.
    (out / "SubmissionEvidence.lean").write_text(
        proof_bytes.decode("utf-8-sig"), encoding="utf-8")
    if tail_proof is not None:
        (out / "SubmissionTail.lean").write_text(
            tail_bytes.decode("utf-8-sig"), encoding="utf-8")
    source, names = admission_source(canonical, tail_proof is not None)
    (out / "SubmissionAdmission.lean").write_text(source, encoding="utf-8")
    audit = "import SubmissionAdmission\n\n" + "\n".join(
        f"#check {n}\n#print axioms {n}" for n in names) + "\n"
    (out / "SubmissionAudit.lean").write_text(audit, encoding="utf-8")
    config = {
        "package": "RH_FINITE_ADMISSION_FRONTIER_433_v0_1_0_FIX6_SUBMISSION",
        "toolchain": "4.33.0",
        "targets": ["SubmissionAdmission"],
        "audit_modules": [{"module": "SubmissionAudit", "theorems": names}],
        "negative_controls": [],
        "source_roots": [str(out.resolve()), ".", "backend"],
        "extra_manifest": str((out / "submission-manifest.json").resolve()),
    }
    if tail_proof is not None:
        config["rh_theorem"] = "SubmissionAdmission.admittedRH"
    config_path = out / "build_config.json"
    config_path.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
    extra = {"files": {p.name: digest_bytes(p.read_bytes())
                       for p in sorted(out.iterdir())
                       if p.is_file() and p.name != "submission-manifest.json"}}
    (out / "submission-manifest.json").write_text(json.dumps(extra, indent=2) + "\n", encoding="utf-8")
    return out, config_path, canonical, names

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("candidate", type=Path)
    ap.add_argument("moment_proof", type=Path)
    ap.add_argument("--tail-proof", type=Path)
    ap.add_argument("--prepare-only", action="store_true",
                    help="Write exact sources only; do not invoke Lean.")
    args = ap.parse_args(argv)
    try:
        out, config, canonical, names = prepare(
            args.candidate.resolve(), args.moment_proof.resolve(),
            args.tail_proof.resolve() if args.tail_proof else None)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as e:
        print("COORDINATE_PREPARATION=FAIL")
        print("ERROR=" + str(e))
        return 2
    print("COORDINATE_SCHEMA=PASS")
    print("SUBMISSION=" + str(out))
    print("MODE=" + canonical["mode"].upper())
    print("ACTUAL_MOMENT_PROOF=REQUIRES_NATIVE_KERNEL_VALIDATION")
    print("TAIL_PROOF=" + ("SUPPLIED_REQUIRES_NATIVE_KERNEL_VALIDATION"
                           if args.tail_proof else "NOT_SUPPLIED"))
    if args.prepare_only:
        print("LEAN_EXECUTION=NONE")
        print("ADMISSION=NOT_ESTABLISHED")
        return 0
    rc = subprocess.call([sys.executable, str(PACKAGE_ROOT / "scripts" / "run_frontier.py"),
                          "--config", str(config)], cwd=str(PACKAGE_ROOT))
    if rc != 0:
        print("SUBMISSION_ADMISSION=NOT_ESTABLISHED")
        return rc
    print("NATIVE_FINITE_ADMISSION=PASS")
    if args.tail_proof:
        print("EXACT_ROOT=SubmissionAdmission.admittedRH : _root_.RiemannHypothesis")
        print("NATIVE_RH_ADMISSION=PASS_EXTERNAL_AUDIT")
    else:
        print("RH_ADMISSION=NOT_ESTABLISHED_NO_TAIL_PROOF")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

