"""Reject changed identity/domain/receipts for the actual all-byte binary pair."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('binary_view', ROOT/'tools/compiler-explorer/equivalence.py')
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)


class BytePredicateEquivalence(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT/'corpus/darkhttpd/equivalence/logencoding/manifest.json').read_text())
        self.pair, = self.manifest['pairs']
        self.left, self.right = self.manifest['endpoints']

    def test_actual_distinct_code_source_spans_and_receipts(self):
        e.validate_pair(self.pair, self.left, self.right)
        for endpoint in [self.left, self.right]:
            e.validate_darkhttpd_build(ROOT, endpoint)
            self.assertEqual(e.c.elf_function((ROOT/endpoint['path']).read_bytes(), 'needs_logencoding'), endpoint['functions']['needs_logencoding'])
            span = endpoint['source']['definitions']['needs_logencoding']
            raw = (ROOT/endpoint['source']['path']).read_bytes()
            self.assertEqual(e.c.sha(raw[span['offset']:span['offset']+span['length']]), span['sha256'])
        self.assertNotEqual(self.left['functions'], self.right['functions'])
        self.assertIsNone(self.pair['value'])

    def test_no_desired_result_frame_or_optimization_substitution(self):
        for key, value in [('left_frame', 16), ('right_frame', 12), ('value', 1), ('function_symbol', 'invented')]:
            pair = copy.deepcopy(self.pair); pair[key] = value
            with self.assertRaises(ValueError):
                e.validate_pair(pair, self.left, self.right)
        right = copy.deepcopy(self.right); right['build']['optimization'] = 'O2'
        with self.assertRaises(ValueError):
            e.validate_pair(self.pair, self.left, right)

    def test_incompatible_build_source_version_target_rejected(self):
        for key, value in [('source_sha256', '0'*64), ('version', '1.16'), ('configuration', 'other'), ('project', 'other'), ('target', 'aarch64-linux-gnu'), ('source_inputs', [])]:
            right = copy.deepcopy(self.right); right['build'][key] = value
            with self.assertRaises(ValueError):
                e.validate_pair(self.pair, self.left, right)
        right = copy.deepcopy(self.right); right['source']['definitions']['needs_logencoding']['offset'] += 1
        with self.assertRaises(ValueError):
            e.validate_pair(self.pair, self.left, right)

    def test_display_must_match_real_receipts(self):
        for key, value in [('cflags', '-O2'), ('compiler', 'invented'), ('configure_args', 'invented'), ('image_id', 'sha256:'+'0'*64), ('source_inputs', []), ('source_sha256', '0'*64)]:
            endpoint = copy.deepcopy(self.right); endpoint['build'][key] = value
            with self.assertRaises(ValueError):
                e.validate_darkhttpd_build(ROOT, endpoint)
        endpoint = copy.deepcopy(self.right); endpoint['sha256'] = '0'*64
        with self.assertRaises(ValueError):
            e.validate_darkhttpd_build(ROOT, endpoint)


if __name__ == '__main__':
    unittest.main()
