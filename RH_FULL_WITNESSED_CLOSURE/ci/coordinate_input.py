#!/usr/bin/env python3
"""Strict finite-coordinate JSON ingestion and numeric-only Lean emission.

The host parser checks syntax and finite data types only.  Actual coordinate
well-formedness is replayed by CoordinateTesting.lean.  Neither stage asserts
an actual-xi enclosure, semantic certificate admission, or RH.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any


# Coordinate integers are mathematical integers, not machine-width values.
# Python 3.11's decimal-conversion guard is not a coordinate-format restriction.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


class CoordinateInputError(ValueError):
    """The input is not an unambiguous instance of the frozen JSON schema."""


ROOT_KEYS = {"spectralCutoff", "etaSplit", "nearCert", "cells", "tailCert"}
RAT_KEYS = {"numerator", "denominator"}
NEAR_KEYS = {"splitPoint", "proofData"}
TAIL_KEYS = {"cutoff", "proofData"}
CELL_KEYS = {
    "left", "right", "g2Lower", "g2Upper", "g3Lower", "g3Upper", "proofData"
}


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            raise CoordinateInputError(f"duplicate JSON key: {key}")
        obj[key] = value
    return obj


def _noninteger(text: str) -> None:
    raise CoordinateInputError(f"non-integer JSON number: {text}")


def _object(value: Any, keys: set[str], path: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise CoordinateInputError(f"{path}: expected object")
    actual = set(value)
    if actual != keys:
        missing = sorted(keys - actual)
        unknown = sorted(actual - keys)
        raise CoordinateInputError(
            f"{path}: field mismatch; missing={missing}; unknown={unknown}"
        )
    return value


def _integer(value: Any, path: str, *, natural: bool = False) -> int:
    # isinstance(True, int) is true; exact type identity prevents coercion.
    if type(value) is not int:
        raise CoordinateInputError(f"{path}: expected integer")
    if natural and value < 0:
        raise CoordinateInputError(f"{path}: expected nonnegative integer")
    return value


def _nat_list(value: Any, path: str) -> list[int]:
    if type(value) is not list:
        raise CoordinateInputError(f"{path}: expected array")
    return [_integer(x, f"{path}[{i}]", natural=True) for i, x in enumerate(value)]


def _rat(value: Any, path: str) -> dict[str, int]:
    obj = _object(value, RAT_KEYS, path)
    return {
        "numerator": _integer(obj["numerator"], f"{path}.numerator"),
        # Zero is legal input data.  Lean, not the host parser, rejects it.
        "denominator": _integer(
            obj["denominator"], f"{path}.denominator", natural=True
        ),
    }


def validate_coordinate(value: Any) -> dict[str, Any]:
    """Validate exact schema/types without claiming semantic admissibility."""
    obj = _object(value, ROOT_KEYS, "coordinate")
    near = _object(obj["nearCert"], NEAR_KEYS, "coordinate.nearCert")
    tail = _object(obj["tailCert"], TAIL_KEYS, "coordinate.tailCert")
    if type(obj["cells"]) is not list:
        raise CoordinateInputError("coordinate.cells: expected array")
    cells = []
    for i, raw in enumerate(obj["cells"]):
        path = f"coordinate.cells[{i}]"
        cell = _object(raw, CELL_KEYS, path)
        cells.append({
            **{key: _rat(cell[key], f"{path}.{key}") for key in (
                "left", "right", "g2Lower", "g2Upper", "g3Lower", "g3Upper"
            )},
            "proofData": _nat_list(cell["proofData"], f"{path}.proofData"),
        })
    return {
        "spectralCutoff": _integer(
            obj["spectralCutoff"], "coordinate.spectralCutoff", natural=True
        ),
        "etaSplit": _rat(obj["etaSplit"], "coordinate.etaSplit"),
        "nearCert": {
            "splitPoint": _rat(near["splitPoint"], "coordinate.nearCert.splitPoint"),
            "proofData": _nat_list(near["proofData"], "coordinate.nearCert.proofData"),
        },
        "cells": cells,
        "tailCert": {
            "cutoff": _integer(tail["cutoff"], "coordinate.tailCert.cutoff", natural=True),
            "proofData": _nat_list(tail["proofData"], "coordinate.tailCert.proofData"),
        },
    }


def parse_coordinate(data: bytes) -> dict[str, Any]:
    """Parse strict UTF-8 JSON: no duplicate keys, floats, or special numbers."""
    try:
        value = json.loads(
            data.decode("utf-8"),
            object_pairs_hook=_pairs,
            parse_float=_noninteger,
            parse_constant=_noninteger,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CoordinateInputError(f"invalid UTF-8 JSON: {exc}") from exc
    return validate_coordinate(value)


def canonical_json(coordinate: dict[str, Any]) -> bytes:
    checked = validate_coordinate(coordinate)
    return json.dumps(
        checked, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _lean_integer(value: int) -> str:
    return f"({value})" if value < 0 else str(value)


def _lean_rat(value: dict[str, int]) -> str:
    return (
        "{ numerator := " + _lean_integer(value["numerator"])
        + ", denominator := " + str(value["denominator"]) + " }"
    )


def _lean_nats(value: list[int]) -> str:
    return "[" + ", ".join(str(n) for n in value) + "]"


def render_lean(coordinate: dict[str, Any]) -> str:
    """Emit a fixed source template whose only variable tokens are integers."""
    obj = validate_coordinate(coordinate)
    near = obj["nearCert"]
    tail = obj["tailCert"]
    cell_text = []
    for cell in obj["cells"]:
        fields = [
            f"{key} := {_lean_rat(cell[key])}" for key in (
                "left", "right", "g2Lower", "g2Upper", "g3Lower", "g3Upper"
            )
        ]
        fields.append("proofData := " + _lean_nats(cell["proofData"]))
        cell_text.append("    { " + ",\n      ".join(fields) + " }")
    rendered_cells = "[\n" + ",\n".join(cell_text) + "\n  ]" if cell_text else "[]"
    digest = hashlib.sha256(canonical_json(obj)).hexdigest()
    return (
        "import CoordinateTesting\n\n"
        "-- FINITE_COORDINATE_VALIDATION_ONLY; RH_ADMISSION=NOT_ESTABLISHED\n"
        f"-- CANONICAL_JSON_SHA256={digest}\n"
        "namespace RHFullWitnessedClosure.CoordinateTesting\n\n"
        "def submittedCoordinate : RHFullWitnessedClosure.RawCert where\n"
        f"  spectralCutoff := {obj['spectralCutoff']}\n"
        f"  etaSplit := {_lean_rat(obj['etaSplit'])}\n"
        "  nearCert := { splitPoint := " + _lean_rat(near["splitPoint"])
        + ", proofData := " + _lean_nats(near["proofData"]) + " }\n"
        f"  cells := {rendered_cells}\n"
        "  tailCert := { cutoff := " + str(tail["cutoff"])
        + ", proofData := " + _lean_nats(tail["proofData"]) + " }\n\n"
        "#eval coordinateCheck submittedCoordinate\n\n"
        "theorem submittedCoordinate_valid :\n"
        "    CoordinateWellFormed submittedCoordinate := by\n"
        "  exact (coordinateCheck_iff submittedCoordinate).mp (by decide)\n\n"
        "#check submittedCoordinate_valid\n"
        "#print axioms RHFullWitnessedClosure.CoordinateTesting.submittedCoordinate_valid\n\n"
        "end RHFullWitnessedClosure.CoordinateTesting\n"
    )


def write_coordinate(source: Path, target: Path) -> dict[str, Any]:
    raw = source.read_bytes()
    coordinate = parse_coordinate(raw)
    rendered = render_lean(coordinate).encode("utf-8")
    metadata: dict[str, Any] = {
        "schema": "RH_FULL_WITNESSED_CLOSURE.RawCert.JSON.v1",
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "canonical_json_sha256": hashlib.sha256(canonical_json(coordinate)).hexdigest(),
        "lean_source_sha256": hashlib.sha256(rendered).hexdigest(),
        "input_bytes": len(raw),
        "host_validation": "JSON_SCHEMA_AND_INTEGER_TYPES_ONLY",
        "lean_coordinate_validation": "PENDING_EXTERNAL_NATIVE_COMPILATION",
        "rh_admission": "NOT_ESTABLISHED",
    }
    # Validate completely before creating or replacing generated files.
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(rendered)
    target.with_name(target.name + ".metadata.json").write_text(
        json.dumps(metadata, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    return metadata


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        metadata = write_coordinate(args.input, args.output)
    except (CoordinateInputError, OSError) as exc:
        print("COORDINATE_INPUT=REJECTED", file=sys.stderr)
        print(f"REASON={exc}", file=sys.stderr)
        return 2
    print("COORDINATE_INPUT=SCHEMA_VALID")
    print("CANONICAL_JSON_SHA256=" + metadata["canonical_json_sha256"])
    print("LEAN_SOURCE_SHA256=" + metadata["lean_source_sha256"])
    print("LEAN_COORDINATE_VALIDATION=PENDING_EXTERNAL_NATIVE_COMPILATION")
    print("RH_ADMISSION=NOT_ESTABLISHED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
