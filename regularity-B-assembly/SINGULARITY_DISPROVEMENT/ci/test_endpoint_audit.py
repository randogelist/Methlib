#!/usr/bin/env python3
"""Check that misleading, incomplete and non-standard audit evidence fails."""
import unittest
from check_endpoint_audit import audit


class AuditChecks(unittest.TestCase):
    name = "SingularityDisprovement.test"

    def transcript(self, axioms="propext, Classical.choice, Quot.sound"):
        return ("EXACT_TYPE_PASS:" + self.name + "\n'" + self.name +
                "' depends on axioms: [" + axioms + "]\n")

    def test_standard(self):
        self.assertEqual(audit(self.transcript(), self.name)["status"], "PASS")

    def test_no_axioms(self):
        text = ("EXACT_TYPE_PASS:" + self.name + "\n'" + self.name +
                "' does not depend on any axioms\n")
        self.assertEqual(audit(text, self.name)["status"], "PASS")

    def test_sorry(self):
        self.assertEqual(audit(self.transcript("sorryAx"), self.name)["status"], "FAIL")

    def test_custom_axiom(self):
        self.assertEqual(audit(self.transcript("SingularClosure.AX6"), self.name)["status"], "FAIL")

    def test_missing_marker(self):
        self.assertEqual(audit(self.transcript().split("\n", 1)[1], self.name)["status"], "FAIL")

    def test_duplicate(self):
        self.assertEqual(audit(self.transcript() * 2, self.name)["status"], "FAIL")

    def test_wrong_name(self):
        self.assertEqual(audit(self.transcript(), self.name + "Other")["status"], "FAIL")

    def test_error(self):
        self.assertEqual(audit(self.transcript() + "x.lean:2:1: error: failure\n", self.name)["status"], "FAIL")

    def test_truncated(self):
        self.assertEqual(audit(self.transcript().replace("]", ""), self.name)["status"], "FAIL")


if __name__ == "__main__":
    unittest.main()
