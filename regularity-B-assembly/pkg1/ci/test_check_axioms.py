#!/usr/bin/env python3
"""Transcript-policy tests only. These tests never invoke Lean."""
from copy import deepcopy
import unittest

from check_axioms import audit


SPEC = {
    "schema_version": 1,
    "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "declarations": [
        {
            "name": name,
            "additional_allowed_axioms": [],
            "required_axioms": [],
            "exact_type_marker": f"EXACT_TYPE_PASS:{name}",
        }
        for name in ("Demo.base", "Demo.axiomFree")
    ],
}
TRANSCRIPT = """"EXACT_TYPE_PASS:Demo.base"
'Demo.base' depends on axioms: [propext,
 Classical.choice, Quot.sound]
EXACT_TYPE_PASS:Demo.axiomFree
'Demo.axiomFree' does not depend on any axioms
"""


class AuditPolicyTests(unittest.TestCase):
    def assert_fails(self, transcript=TRANSCRIPT, spec=None):
        result = audit(transcript, deepcopy(SPEC) if spec is None else spec)
        self.assertEqual(result["status"], "FAIL", result)
        self.assertTrue(result["errors"])

    def test_quoted_and_bare_markers_with_multiline_axioms(self):
        result = audit(TRANSCRIPT, SPEC)
        self.assertEqual(result["status"], "PASS", result)
        self.assertEqual(result["declaration_count"], 2)
        self.assertFalse(result["endpoint_completion_inferred"])

    def test_bare_declaration_names(self):
        transcript = TRANSCRIPT.replace("'Demo.base'", "Demo.base").replace("'Demo.axiomFree'", "Demo.axiomFree")
        self.assertEqual(audit(transcript, SPEC)["status"], "PASS")

    def test_missing_report(self):
        self.assert_fails(TRANSCRIPT.replace("'Demo.axiomFree' does not depend on any axioms\n", ""))

    def test_duplicate_report(self):
        self.assert_fails(TRANSCRIPT + "'Demo.axiomFree' does not depend on any axioms\n")

    def test_unexpected_report(self):
        self.assert_fails(TRANSCRIPT + "'Demo.other' does not depend on any axioms\n")

    def test_malformed_report(self):
        self.assert_fails(TRANSCRIPT + "'Demo.other' depends on axioms: [propext\n")

    def test_embedded_report_text_is_not_a_report(self):
        self.assert_fails(TRANSCRIPT.replace("'Demo.base' depends", "message contains 'Demo.base' depends"))

    def test_custom_axiom(self):
        self.assert_fails(TRANSCRIPT.replace("Classical.choice", "Demo.assumedRegularity"))

    def test_axiom_names_are_case_sensitive(self):
        self.assert_fails(TRANSCRIPT.replace("Classical.choice", "Classical.Choice"))

    def test_sorry_axiom(self):
        self.assert_fails(TRANSCRIPT.replace("propext", "sorryAx"))

    def test_sorry_warning(self):
        self.assert_fails(TRANSCRIPT + "warning: declaration uses 'sorry'\n")

    def test_compiler_error(self):
        self.assert_fails(TRANSCRIPT + "Audit.lean:2:1: error: type mismatch\n")

    def test_missing_exact_type_marker(self):
        self.assert_fails(TRANSCRIPT.replace('"EXACT_TYPE_PASS:Demo.base"\n', ""))

    def test_duplicate_quoted_and_bare_marker(self):
        self.assert_fails(TRANSCRIPT + "EXACT_TYPE_PASS:Demo.base\n")

    def test_unmatched_marker_quote(self):
        self.assert_fails(TRANSCRIPT.replace('"EXACT_TYPE_PASS:Demo.base"', '"EXACT_TYPE_PASS:Demo.base'))

    def test_marker_must_identify_its_declaration(self):
        spec = deepcopy(SPEC)
        spec["declarations"][1]["exact_type_marker"] = "EXACT_TYPE_PASS:Demo.base"
        self.assert_fails(spec=spec)

    def test_additional_allowance_rejected(self):
        spec = deepcopy(SPEC)
        spec["declarations"][0]["additional_allowed_axioms"] = ["Demo.assumedRegularity"]
        self.assert_fails(spec=spec)

    def test_missing_required_axiom(self):
        spec = deepcopy(SPEC)
        spec["declarations"][1]["required_axioms"] = ["propext"]
        self.assert_fails(spec=spec)

    def test_changed_standard_axiom_policy(self):
        spec = deepcopy(SPEC)
        spec["standard_axioms"].append("Demo.assumedRegularity")
        self.assert_fails(spec=spec)

    def test_duplicate_expected_declaration(self):
        spec = deepcopy(SPEC)
        spec["declarations"].append(deepcopy(spec["declarations"][0]))
        self.assert_fails(spec=spec)

    def test_malformed_specifications_fail_closed(self):
        bad_specs = [[], {}, {**deepcopy(SPEC), "declarations": [None]},
                     {**deepcopy(SPEC), "standard_axioms": None},
                     {**deepcopy(SPEC), "schema_version": True}]
        malformed_entry = deepcopy(SPEC)
        malformed_entry["declarations"][0]["required_axioms"] = None
        bad_specs.append(malformed_entry)
        for spec in bad_specs:
            with self.subTest(spec=spec):
                self.assert_fails(spec=spec)


if __name__ == "__main__":
    unittest.main()
