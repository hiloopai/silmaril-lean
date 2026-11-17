"""Corpus database integration: real inputs, additive backup, no ELF blob storage."""
import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import matrix
import database
from census import report_relative_path
from matrix import inventory

ROOT = Path(__file__).resolve().parents[2]


class CorpusDatabase(unittest.TestCase):
    def test_checked_variant_modules_are_bound(self):
        artifacts = inventory(ROOT)['artifacts']
        self.assertEqual(sum(a['lean_status'].startswith('variant: whole-file') for a in artifacts), 64)
        check = json.loads((ROOT / 'corpus/measurements/variant-lean/checks.json').read_text())['artifacts'][0]
        source = ROOT / next(iter(check['module_sha256']))
        original = matrix.sha
        with patch.object(matrix, 'sha', side_effect=lambda path: 'stale' if path == source else original(path)):
            with self.assertRaisesRegex(ValueError, 'changed since measured Lean check'):
                inventory(ROOT)

    def test_concrete_function_statement_binding(self):
        data = inventory(ROOT)
        self.assertEqual(data['formal_statement_counts'], {'contextual_c_to_elf': 4, 'functional_equivalence': 1})
        participants = [a for a in data['artifacts'] if a['functional_equivalence_statements']]
        self.assertEqual(len(participants), 2)
        self.assertEqual({a['project'] for a in participants}, {'mimalloc'})
        source_participants = [a for a in data['artifacts'] if a['contextual_c_to_elf_statements']]
        self.assertEqual([a['path'] for a in source_participants], ['corpus/elf/mimalloc/x86_64/libmimalloc.so.2.1', 'corpus/elf/openssl/x86_64/libssl.so.3'])
        check = json.loads((ROOT / 'corpus/measurements/formal-functions/checks.json').read_text())['statements'][0]
        source = ROOT / next(iter(check['module_sha256']))
        original = matrix.sha
        with patch.object(matrix, 'sha', side_effect=lambda path: 'stale' if path == source else original(path)):
            with self.assertRaisesRegex(ValueError, 'changed since formal statement check'):
                inventory(ROOT)

    def test_stale_source_semantics_rejected(self):
        source = ROOT / 'corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/mi_version/definition.c'
        original = matrix.sha
        with patch.object(matrix, 'sha', side_effect=lambda path: 'stale' if path == source else original(path)):
            with self.assertRaisesRegex(ValueError, 'changed since formal statement check'):
                inventory(ROOT)

    def test_stale_census_rejected(self):
        artifact = inventory(ROOT)['artifacts'][0]
        original = json.loads((ROOT / 'corpus/census' / report_relative_path(artifact['path'])).read_text())
        for field in ['sha256', 'path', 'receipt_sha256']:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                report = json.loads(json.dumps(original))
                if field == 'receipt_sha256':
                    report['identity'][field] = 'stale'
                else:
                    report[field] = 'stale'
                path = root / 'corpus/census' / report_relative_path(artifact['path'])
                path.parent.mkdir(parents=True)
                path.write_text(json.dumps(report))
                with self.assertRaisesRegex(ValueError, 'census artifact or receipt identity mismatch'):
                    database.artifact_census(root, artifact)

    def test_real_inputs_and_preserved_base(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, output = Path(tmp) / 'base.sqlite', Path(tmp) / 'corpus.sqlite'
            db = sqlite3.connect(base)
            db.executescript('CREATE TABLE preserve(value TEXT); INSERT INTO preserve VALUES("unchanged");')
            db.close()
            before = hashlib.sha256(base.read_bytes()).hexdigest()
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/database.py'), '--base', str(base), '--output', str(output)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(before, hashlib.sha256(base.read_bytes()).hexdigest())
            db = sqlite3.connect(output)
            self.assertEqual(db.execute('SELECT value FROM preserve').fetchone(), ('unchanged',))
            self.assertGreaterEqual(db.execute('SELECT count(*) FROM corpus_artifacts').fetchone()[0], 54)
            self.assertEqual(db.execute("SELECT count(*) FROM corpus_artifacts WHERE metadata LIKE '%whole-file parse unavailable%'").fetchone()[0], 3)
            for metadata, census in db.execute('SELECT metadata,census FROM corpus_artifacts'):
                artifact = json.loads(metadata)
                self.assertIsNotNone(census, artifact['path'])
                report = json.loads(census)
                self.assertEqual(report['sha256'], artifact['sha256'])
                self.assertEqual(report['path'], artifact['path'])
            bound = db.execute("SELECT mapping FROM corpus_functions WHERE symbol='mi_version'").fetchall()
            self.assertEqual(sum('concrete contextual C-to-ELF statement' in row[0] for row in bound), 1)
            for name in ['_mi_arena_id_none', '_mi_allocator_done']:
                rows = db.execute('SELECT mapping FROM corpus_functions WHERE symbol=?', (name,)).fetchall()
                self.assertEqual(sum('concrete contextual C-to-ELF statement' in row[0] for row in rows), 1)
            self.assertGreater(db.execute('SELECT count(*) FROM corpus_functions').fetchone()[0], 42000)
            self.assertGreater(db.execute('SELECT count(*) FROM corpus_timings').fetchone()[0], 10)
            self.assertTrue(all(row[2].upper() != 'BLOB' for row in db.execute('PRAGMA table_info(corpus_artifacts)')))
            db.close()
            again = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/database.py'), '--output', str(output)], capture_output=True)
            self.assertNotEqual(again.returncode, 0)


if __name__ == '__main__':
    unittest.main()
