#!/usr/bin/env python3
"""Exercise the fail-closed audit boundary; no Lean execution."""
import copy
import unittest

from check_axioms import audit
from check_sources import lean_code


class AuditBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.spec = {
            "schema_version": 1,
            "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "declarations": [{
                "name": "SingularClosure.checked", "additional_allowed_axioms": [],
                "required_axioms": [], "exact_type_marker": "EXACT_TYPE_PASS:checked",
            }],
        }
        self.log = "EXACT_TYPE_PASS:checked\n'SingularClosure.checked' depends on axioms: [propext, Classical.choice, Quot.sound]\n"

    def test_valid_audit(self):
        self.assertEqual(audit(self.log, self.spec)["status"], "PASS")

    def test_missing_report(self):
        self.assertEqual(audit("EXACT_TYPE_PASS:checked\n", self.spec)["status"], "FAIL")

    def test_missing_exact_type_check(self):
        self.assertEqual(audit(self.log.split("\n", 1)[1], self.spec)["status"], "FAIL")

    def test_duplicate_report(self):
        self.assertEqual(audit(self.log + self.log, self.spec)["status"], "FAIL")

    def test_sorry_rejected(self):
        self.assertEqual(audit(self.log.replace("Quot.sound", "sorryAx"), self.spec)["status"], "FAIL")

    def test_unknown_axiom_rejected(self):
        self.assertEqual(audit(self.log.replace("Quot.sound", "Hidden.AnalyticBridge"), self.spec)["status"], "FAIL")

    def test_empty_audit_rejected(self):
        spec = copy.deepcopy(self.spec)
        spec["declarations"] = []
        self.assertEqual(audit("", spec)["status"], "FAIL")

    def test_exact_custom_axiom_policy(self):
        spec = copy.deepcopy(self.spec)
        spec["declarations"][0]["additional_allowed_axioms"] = ["SingularClosure.AX6"]
        spec["declarations"][0]["required_axioms"] = ["SingularClosure.AX6"]
        self.assertEqual(audit(self.log, spec)["status"], "FAIL")
        log = self.log.replace("Quot.sound]", "Quot.sound, SingularClosure.AX6]")
        self.assertEqual(audit(log, spec)["status"], "PASS")

    def test_no_axiom_report_supported(self):
        log = "EXACT_TYPE_PASS:checked\n'SingularClosure.checked' does not depend on any axioms\n"
        self.assertEqual(audit(log, self.spec)["status"], "PASS")

    def test_nested_comment_and_string_stripping(self):
        source = '/- outer /- sorry -/ axiom -/\n-- admit\n#eval IO.println "sorryAx"\ntheorem actual := by sorry\n'
        code = lean_code(source)
        self.assertEqual(code.count("sorry"), 1)
        self.assertEqual(code.count("\n"), source.count("\n"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
