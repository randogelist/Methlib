#!/usr/bin/env python3
"""Fail-closed scheduler tests. Every subprocess is mocked; no Lean execution."""
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_critical as scheduler


class SchedulerTests(unittest.TestCase):
    def setUp(self):
        self.old_directory = Path.cwd()
        self.directory = tempfile.TemporaryDirectory()
        os.chdir(self.directory.name)
        Path('ci/critical_audits').mkdir(parents=True)
        Path('SingularClosure').mkdir()
        self.base = 'SingularClosure.Base'
        self.root = scheduler.ROOT_MODULE
        Path('ci/critical_modules.txt').write_text(self.base + '\n' + self.root + '\n')
        Path('SingularClosure/Base.lean').write_text('-- fixture\n')
        Path('SingularClosure/SmallDataClosure.lean').write_text('import ' + self.base + '\n')
        self.manifest = {'schema_version': 1, 'required_modules': [self.root]}
        self.write_manifest()
        self.audit = Path('ci/critical_audits/SmallDataClosure')
        self.audit.with_suffix('.lean').write_text('-- mocked audit\n')
        self.audit.with_suffix('.json').write_text(json.dumps({
            'declarations': [{'name': scheduler.ROOT_DECLARATION}]}))

    def tearDown(self):
        os.chdir(self.old_directory)
        self.directory.cleanup()

    def write_manifest(self):
        Path('ci/critical_required_audits.json').write_text(json.dumps(self.manifest))

    def execute(self, results=None):
        results = iter(results or [])
        calls = []

        class Process:
            def __init__(self, code, text):
                self.code = code
                self.stdout = io.StringIO(text)

            def wait(self):
                return self.code

        def fake_popen(command, **kwargs):
            calls.append(command)
            result = next(results, (0, ''))
            if isinstance(result, Exception):
                raise result
            return Process(*result)

        with patch.object(scheduler.subprocess, 'Popen', side_effect=fake_popen), \
                contextlib.redirect_stdout(io.StringIO()):
            code = scheduler.main()
        report = json.loads(scheduler.STATUS_PATH.read_text())
        return code, report, calls

    def assert_preflight_failure(self):
        code, report, calls = self.execute()
        self.assertEqual(code, 1)
        self.assertEqual(report['status'], 'FAIL')
        self.assertEqual(report['bulk_build'], 'NOT_RUN')
        self.assertTrue(report['errors'])
        self.assertEqual(calls, [])

    def test_full_success_requires_all_four_calls(self):
        code, report, calls = self.execute()
        self.assertEqual(code, 0)
        self.assertEqual(report['audit_coverage'], 'PASS')
        self.assertEqual(report['audits'], {self.root: 'PASS'})
        self.assertEqual(len(calls), 4)
        self.assertEqual(calls[0], ['lake', 'build', self.base, self.root])
        self.assertEqual(calls[1], ['lake', 'build', self.root])
        self.assertEqual(calls[2][:3], ['lake', 'env', 'lean'])
        self.assertEqual(calls[3][1], 'ci/check_axioms.py')

    def test_bulk_failure_even_when_endpoint_audit_passes(self):
        code, report, _ = self.execute([(1, 'Built SingularClosure.SmallDataClosure PASS\n')])
        self.assertEqual(code, 1)
        self.assertEqual(report['audits'][self.root], 'PASS')
        self.assertEqual(report['bulk_build'], 'FAIL')

    def test_diagnostic_error_only_blocks(self):
        code, report, calls = self.execute([(1, 'error: SingularClosure/Base.lean:1: broken\n')])
        self.assertEqual(code, 1)
        self.assertEqual(report['audits'][self.root], 'BLOCKED')
        self.assertEqual(len(calls), 1)

    def test_endpoint_build_failure(self):
        code, report, calls = self.execute([(0, ''), (1, '')])
        self.assertEqual((code, report['audits'][self.root], len(calls)), (1, 'FAIL', 2))

    def test_lean_audit_failure(self):
        code, report, calls = self.execute([(0, ''), (0, ''), (1, '')])
        self.assertEqual((code, report['audits'][self.root], len(calls)), (1, 'FAIL', 3))

    def test_axiom_checker_failure(self):
        code, report, calls = self.execute([(0, ''), (0, ''), (0, ''), (1, '')])
        self.assertEqual((code, report['audits'][self.root], len(calls)), (1, 'FAIL', 4))

    def test_process_launch_failure(self):
        code, report, _ = self.execute([OSError('compiler unavailable')])
        self.assertEqual(code, 1)
        self.assertIn('compiler unavailable', report['errors'])

    def test_missing_manifest(self):
        Path('ci/critical_required_audits.json').unlink()
        self.assert_preflight_failure()

    def test_malformed_manifest(self):
        Path('ci/critical_required_audits.json').write_text('{')
        self.assert_preflight_failure()

    def test_unsupported_manifest(self):
        self.manifest['schema_version'] = 2
        self.write_manifest()
        self.assert_preflight_failure()

    def test_empty_required_audits(self):
        self.manifest['required_modules'] = []
        self.write_manifest()
        self.assert_preflight_failure()

    def test_duplicate_required_audit(self):
        self.manifest['required_modules'] *= 2
        self.write_manifest()
        self.assert_preflight_failure()

    def test_unknown_required_module(self):
        self.manifest['required_modules'].append('SingularClosure.Unknown')
        self.write_manifest()
        self.assert_preflight_failure()

    def test_root_required(self):
        self.manifest['required_modules'] = [self.base]
        self.write_manifest()
        self.assert_preflight_failure()

    def test_root_declaration_required(self):
        self.audit.with_suffix('.json').write_text('{"declarations": []}')
        self.assert_preflight_failure()

    def test_missing_lean_audit(self):
        self.audit.with_suffix('.lean').unlink()
        self.assert_preflight_failure()

    def test_missing_json_policy(self):
        self.audit.with_suffix('.json').unlink()
        self.assert_preflight_failure()

    def test_undeclared_extra_audit(self):
        Path('ci/critical_audits/Extra.lean').write_text('-- stale\n')
        self.assert_preflight_failure()

    def test_undeclared_extra_policy(self):
        Path('ci/critical_audits/Extra.json').write_text('{}')
        self.assert_preflight_failure()

    def test_audit_basename_collision(self):
        extra = 'Other.SmallDataClosure'
        self.manifest['required_modules'].append(extra)
        self.write_manifest()
        with Path('ci/critical_modules.txt').open('a') as output:
            output.write(extra + '\n')
        self.assert_preflight_failure()

    def test_empty_module_list(self):
        Path('ci/critical_modules.txt').write_text('')
        self.assert_preflight_failure()

    def test_duplicate_modules(self):
        with Path('ci/critical_modules.txt').open('a') as output:
            output.write(self.root + '\n')
        self.assert_preflight_failure()

    def test_missing_source(self):
        Path('SingularClosure/Base.lean').unlink()
        self.assert_preflight_failure()

    def test_import_cycle(self):
        Path('SingularClosure/Base.lean').write_text('import ' + self.root + '\n')
        self.assert_preflight_failure()

    def test_stale_pass_overwritten_on_preflight_failure(self):
        Path('evidence').mkdir()
        scheduler.STATUS_PATH.write_text('{"status": "PASS"}')
        self.audit.with_suffix('.lean').unlink()
        self.assert_preflight_failure()
        self.assertEqual(json.loads(scheduler.STATUS_PATH.read_text())['status'], 'FAIL')

    def test_exact_final_audit_coverage(self):
        # Simulate a corrupted plan after validation: no required endpoint is visited.
        with patch.object(scheduler, 'load_plan', return_value=([self.base], {self.base: []}, [self.root])):
            code, report, calls = self.execute()
        self.assertEqual((code, report['audit_coverage'], len(calls)), (1, 'FAIL', 1))
        self.assertEqual(report['audits'], {})


if __name__ == '__main__':
    unittest.main(verbosity=2)
