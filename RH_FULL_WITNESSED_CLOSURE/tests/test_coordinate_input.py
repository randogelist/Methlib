from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("coordinate_input", ROOT / "ci/coordinate_input.py")
assert SPEC is not None and SPEC.loader is not None
ci = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ci)


class CoordinateInputTests(unittest.TestCase):
    def setUp(self) -> None:
        self.example = json.loads((ROOT / "coordinates/example.json").read_text(encoding="utf-8"))

    def parse(self, value):
        return ci.parse_coordinate(json.dumps(value).encode("utf-8"))

    def test_frozen_schema_and_example_are_round_trippable(self) -> None:
        parsed = self.parse(self.example)
        self.assertEqual(ci.parse_coordinate(ci.canonical_json(parsed)), parsed)
        lean = ci.render_lean(parsed)
        self.assertIn("import CoordinateTesting\n", lean)
        self.assertIn("numerator := (-1)", lean)
        self.assertIn("(coordinateCheck_iff submittedCoordinate).mp (by decide)", lean)
        self.assertIn("RH_ADMISSION=NOT_ESTABLISHED", lean)

    def test_rejects_source_injection_in_every_scalar_class(self) -> None:
        for path in [("spectralCutoff",), ("etaSplit", "numerator"),
                     ("etaSplit", "denominator")]:
            with self.subTest(path=path):
                value = copy.deepcopy(self.example)
                parent = value
                for key in path[:-1]:
                    parent = parent[key]
                parent[path[-1]] = "0\naxiom forged : False"
                with self.assertRaises(ci.CoordinateInputError):
                    self.parse(value)
        value = copy.deepcopy(self.example)
        value["tailCert"]["proofData"] = ["0]; axiom forged : False"]
        with self.assertRaises(ci.CoordinateInputError):
            self.parse(value)

    def test_rejects_float_and_bool_coercion(self) -> None:
        for invalid in [True, False, 1.0, 1.5, "1", None]:
            for location in ["spectralCutoff", "numerator", "proofData"]:
                with self.subTest(invalid=invalid, location=location):
                    value = copy.deepcopy(self.example)
                    if location == "spectralCutoff":
                        value[location] = invalid
                    elif location == "numerator":
                        value["etaSplit"][location] = invalid
                    else:
                        value["nearCert"][location] = [invalid]
                    with self.assertRaises(ci.CoordinateInputError):
                        self.parse(value)

    def test_rejects_nonstandard_json_numbers(self) -> None:
        raw = json.dumps(self.example)
        for text in ["NaN", "Infinity", "-Infinity", "1e2", "2.0"]:
            with self.subTest(text=text):
                changed = raw.replace('"spectralCutoff": 16', '"spectralCutoff": ' + text)
                with self.assertRaises(ci.CoordinateInputError):
                    ci.parse_coordinate(changed.encode("utf-8"))

    def test_rejects_unknown_missing_and_duplicate_keys(self) -> None:
        value = copy.deepcopy(self.example)
        value["trusted"] = True
        with self.assertRaises(ci.CoordinateInputError):
            self.parse(value)
        value = copy.deepcopy(self.example)
        del value["cells"][0]["g3Upper"]
        with self.assertRaises(ci.CoordinateInputError):
            self.parse(value)
        value = copy.deepcopy(self.example)
        value["etaSplit"]["extra"] = 1
        with self.assertRaises(ci.CoordinateInputError):
            self.parse(value)
        raw = json.dumps(self.example)
        raw = raw.replace('"spectralCutoff": 16', '"spectralCutoff": 16, "spectralCutoff": 17')
        with self.assertRaises(ci.CoordinateInputError):
            ci.parse_coordinate(raw.encode("utf-8"))

    def test_zero_denominator_is_deferred_to_lean(self) -> None:
        self.example["etaSplit"]["denominator"] = 0
        parsed = self.parse(self.example)
        self.assertIn("denominator := 0", ci.render_lean(parsed))
        self.example["etaSplit"]["denominator"] = -1
        with self.assertRaises(ci.CoordinateInputError):
            self.parse(self.example)

    def test_unbounded_integer_precision_is_preserved(self) -> None:
        huge = 10 ** 5000 + 17
        self.example["spectralCutoff"] = huge
        self.example["etaSplit"]["numerator"] = -huge
        self.example["tailCert"]["proofData"] = [huge]
        parsed = self.parse(self.example)
        self.assertEqual(parsed["spectralCutoff"], huge)
        lean = ci.render_lean(parsed)
        self.assertIn("spectralCutoff := " + str(huge), lean)
        self.assertIn("numerator := (" + str(-huge) + ")", lean)

    def test_canonical_hash_and_source_ignore_json_key_order_and_spacing(self) -> None:
        original = self.parse(self.example)
        alternate = ci.parse_coordinate(json.dumps(self.example, sort_keys=True, indent=4).encode())
        self.assertEqual(ci.canonical_json(original), ci.canonical_json(alternate))
        self.assertEqual(ci.render_lean(original), ci.render_lean(alternate))

    def test_cli_writes_exact_provenance_and_no_lean_process(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            source = directory / "input.json"
            target = directory / "SubmittedCoordinate.lean"
            raw = json.dumps(self.example, indent=2).encode("utf-8")
            source.write_bytes(raw)
            result = subprocess.run(
                [sys.executable, str(ROOT / "ci/coordinate_input.py"),
                 "--input", str(source), "--output", str(target)],
                text=True, capture_output=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            metadata = json.loads(target.with_name(target.name + ".metadata.json").read_text())
            self.assertEqual(metadata["input_sha256"], hashlib.sha256(raw).hexdigest())
            self.assertEqual(metadata["lean_source_sha256"], hashlib.sha256(target.read_bytes()).hexdigest())
            self.assertEqual(metadata["canonical_json_sha256"], hashlib.sha256(ci.canonical_json(self.example)).hexdigest())
            self.assertEqual(metadata["rh_admission"], "NOT_ESTABLISHED")
            self.assertIn("PENDING_EXTERNAL_NATIVE_COMPILATION", result.stdout)

    def test_rejected_input_does_not_replace_existing_output(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            source = directory / "invalid.json"
            target = directory / "SubmittedCoordinate.lean"
            source.write_text('{"spectralCutoff": true}', encoding="utf-8")
            target.write_text("existing output\n", encoding="utf-8")
            with self.assertRaises(ci.CoordinateInputError):
                ci.write_coordinate(source, target)
            self.assertEqual(target.read_text(), "existing output\n")
            self.assertFalse(target.with_name(target.name + ".metadata.json").exists())


if __name__ == "__main__":
    unittest.main()
