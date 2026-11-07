from __future__ import annotations

from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


PACKAGE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("run_coordinates", PACKAGE / "ci/run_coordinates.py")
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class AxiomEvidenceTests(unittest.TestCase):
    """Evidence must not be accepted from missing, ambiguous, or tainted reports."""

    short = "submittedCoordinate_valid"

    @property
    def name(self) -> str:
        return runner.NS + self.short

    @property
    def clean(self) -> str:
        return f"'{self.name}' does not depend on any axioms\n"

    def check(self, text: str) -> None:
        with redirect_stdout(io.StringIO()):
            runner.audit_axioms(text, [self.short])

    def test_accepts_standard_axioms_in_lean_multiline_format(self) -> None:
        self.check(
            f"'{self.name}' depends on axioms: [propext,\n"
            " Classical.choice, Quot.sound]\n"
        )

    def test_accepts_explicit_empty_reports(self) -> None:
        self.check(self.clean)
        self.check(f"'{self.name}' depends on axioms: []\n")

    def test_rejects_missing_or_different_declaration_report(self) -> None:
        for text in ["", "RUN=PASS\n", self.clean.replace(self.short, "anotherTheorem")]:
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    self.check(text)

    def test_rejects_sorry_and_unapproved_axioms(self) -> None:
        for text in [
            f"'{self.name}' depends on axioms: [sorryAx]\n",
            f"'{self.name}' depends on axioms: [propext, CandidateTrust]\n",
            self.clean + "warning: declaration 'other' uses sorryAx\n",
        ]:
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    self.check(text)

    def test_rejects_contradictory_clean_and_tainted_reports(self) -> None:
        tainted = f"'{self.name}' depends on axioms: [CandidateTrust]\n"
        for text in [self.clean + tainted, tainted + self.clean]:
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    self.check(text)

    def test_rejects_duplicate_reports(self) -> None:
        standard = f"'{self.name}' depends on axioms: [propext]\n"
        for text in [self.clean * 2, standard * 2, self.clean + standard]:
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    self.check(text)

    def test_rejects_report_shaped_substrings_and_malformed_suffixes(self) -> None:
        for text in [
            "warning: quoted text " + self.clean,
            self.clean.rstrip("\n") + " [CandidateTrust]\n",
            f"'{self.name}' depends on axioms: [propext] unexpected suffix\n",
        ]:
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    self.check(text)


class SourceOnlyTests(unittest.TestCase):
    def write_manifest(self, root: Path, entry: str = "CoordinateData.lean") -> None:
        source = root / "CoordinateData.lean"
        source.write_text("-- Host fixture; never compiled.\n", encoding="utf-8")
        (root / "provenance").mkdir()
        (root / "provenance/source-manifest.sha256").write_text(
            hashlib.sha256(source.read_bytes()).hexdigest() + "  " + entry + "\n",
            encoding="utf-8",
        )

    def test_check_source_verifies_bytes_without_launching_any_process(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.write_manifest(root)
            with mock.patch.object(runner, "ROOT", root), \
                 mock.patch.object(sys, "argv", ["run_coordinates.py", "--check-source"]), \
                 mock.patch.object(runner.subprocess, "run", side_effect=AssertionError("process forbidden")) as launch, \
                 redirect_stdout(io.StringIO()) as output:
                self.assertEqual(runner.main(), 0)
            launch.assert_not_called()
            self.assertIn("SOURCE_MANIFEST=PASS", output.getvalue())
            self.assertFalse((root / "evidence").exists())

    def test_check_source_fails_on_changed_bytes_before_any_process(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.write_manifest(root)
            (root / "CoordinateData.lean").write_text("-- Changed after freeze.\n", encoding="utf-8")
            with mock.patch.object(runner, "ROOT", root), \
                 mock.patch.object(sys, "argv", ["run_coordinates.py", "--check-source"]), \
                 mock.patch.object(runner.subprocess, "run", side_effect=AssertionError("process forbidden")) as launch:
                with self.assertRaises(ValueError):
                    runner.main()
            launch.assert_not_called()

    def test_manifest_rejects_paths_outside_package(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            parent = Path(d)
            root = parent / "package"
            root.mkdir()
            self.write_manifest(root, "../outside.lean")
            (parent / "outside.lean").write_bytes((root / "CoordinateData.lean").read_bytes())
            with mock.patch.object(runner, "ROOT", root):
                with self.assertRaises(ValueError):
                    runner.verify_manifest()


if __name__ == "__main__":
    unittest.main()
