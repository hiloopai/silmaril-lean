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
        self.assertEqual(sum(a['lean_status'].startswith('variant: whole-file') for a in artifacts), 227)
        check = json.loads((ROOT / 'corpus/measurements/variant-lean/checks.json').read_text())['artifacts'][0]
        source = ROOT / next(iter(check['module_sha256']))
        original = matrix.sha
        with patch.object(matrix, 'sha', side_effect=lambda path: 'stale' if path == source else original(path)):
            with self.assertRaisesRegex(ValueError, 'changed since measured Lean check'):
                inventory(ROOT)

    def test_concrete_function_statement_binding(self):
        data = inventory(ROOT)
        self.assertEqual(data['binary_viewer_statement_count'], 16)
        self.assertEqual(data['formal_statement_counts'], {'contextual_c_to_elf': 32, 'functional_equivalence': 16})
        participants = [a for a in data['artifacts'] if a['functional_equivalence_statements']]
        self.assertEqual(len(participants), 20)
        self.assertEqual({a['project'] for a in participants}, {'mimalloc', 'tinycc', 'sqlite', 'cjson', 'darkhttpd'})
        source_participants = [a for a in data['artifacts'] if a['contextual_c_to_elf_statements']]
        self.assertEqual([a['path'] for a in source_participants], ['corpus/elf/cjson/x86_64/libcjson.so.1', 'corpus/elf/mimalloc/x86_64/libmimalloc.so.2.1', 'corpus/elf/openssl/x86_64/libssl.so.3', 'corpus/elf/sqlite/x86_64/libsqlite3.so', 'corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1', 'corpus/variants/darkhttpd/1.17/default/x86_64/O0/unstripped/darkhttpd', 'corpus/variants/tinycc/0.9.27/default/x86_64/O0/unstripped/tcc'])
        statements = json.loads((ROOT / 'corpus/measurements/formal-functions/checks.json').read_text())['statements']
        cjson = [s for s in statements if s['declaration'].startswith('Silmaril.Elf.Corpus.CjsonTypePredicates.')]
        self.assertEqual({s['function_symbol'] for s in cjson}, {
            'cJSON_IsNull', 'cJSON_IsBool', 'cJSON_IsNumber',
            'cJSON_IsString', 'cJSON_IsArray', 'cJSON_IsObject',
            'cJSON_IsInvalid', 'cJSON_IsFalse', 'cJSON_IsTrue', 'cJSON_IsRaw'})
        self.assertEqual({s['function_address'] for s in cjson}, {21600, 21568, 21632, 21712, 21776, 21808, 21472, 21504, 21536, 21840})
        self.assertTrue(all(set(s['artifact_sha256']) == {'corpus/elf/cjson/x86_64/libcjson.so.1'} for s in cjson))
        os_getters = [s for s in statements if s['declaration'].startswith('Silmaril.Elf.Corpus.MimallocOsGlobals.')]
        self.assertEqual({(s['function_symbol'], s['function_address']) for s in os_getters}, {
            ('_mi_os_page_size', 62000), ('_mi_os_large_page_size', 62016)})
        self.assertTrue(all(set(s['artifact_sha256']) == {'corpus/elf/mimalloc/x86_64/libmimalloc.so.2.1'} for s in os_getters))
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

    def test_measurement_identity_merge(self):
        receipt = next((ROOT / 'corpus/measurements/formal-functions/runs').glob('*.json'))
        original = json.loads(receipt.read_text())
        with tempfile.TemporaryDirectory() as tmp:
            first, second = Path(tmp) / 'formal.json', Path(tmp) / 'structural.json'
            first.write_text(json.dumps(original))
            second.write_text(json.dumps(original))
            self.assertEqual(list(database.measurement_runs([first, second])), [original])
            conflicting = {**original, 'wall_seconds': original['wall_seconds'] + 1}
            second.write_text(json.dumps(conflicting))
            with self.assertRaisesRegex(ValueError, 'conflicting measurements for run'):
                list(database.measurement_runs([first, second]))

    def test_real_inputs_and_preserved_base(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, output = Path(tmp) / 'base.sqlite', Path(tmp) / 'corpus.sqlite'
            db = sqlite3.connect(base)
            db.executescript('CREATE TABLE preserve(value TEXT); INSERT INTO preserve VALUES("unchanged");')
            db.close()
            before = hashlib.sha256(base.read_bytes()).hexdigest()
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/database.py'), '--base', str(base), '--output', str(output), '--source-rev', '1' * 40], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(before, hashlib.sha256(base.read_bytes()).hexdigest())
            db = sqlite3.connect(output)
            self.assertEqual(db.execute("SELECT value FROM corpus_meta WHERE key='revision'").fetchone()[0], '1' * 40)
            self.assertEqual(db.execute('SELECT value FROM preserve').fetchone(), ('unchanged',))
            self.assertGreaterEqual(db.execute('SELECT count(*) FROM corpus_artifacts').fetchone()[0], 54)
            self.assertEqual(db.execute("SELECT count(*) FROM corpus_artifacts WHERE metadata LIKE '%whole-file parse unavailable%'").fetchone()[0], 0)
            for metadata, census in db.execute('SELECT metadata,census FROM corpus_artifacts'):
                artifact = json.loads(metadata)
                self.assertIsNotNone(census, artifact['path'])
                report = json.loads(census)
                self.assertEqual(report['sha256'], artifact['sha256'])
                self.assertEqual(report['path'], artifact['path'])
            bound = db.execute("SELECT mapping FROM corpus_functions WHERE symbol='mi_version'").fetchall()
            self.assertEqual(sum('concrete contextual C-to-ELF statement' in row[0] for row in bound), 1)
            binary_bound = [json.loads(row[0]) for row in bound if any(s['kind'] == 'functional_equivalence' for s in json.loads(row[0]).get('formal_statements', []))]
            self.assertEqual(len(binary_bound), 8)
            self.assertTrue(all('tv_context' not in row or 'concrete contextual' not in row['tv_context'].get('status', '') for row in binary_bound))
            for name in ['_mi_arena_id_none', '_mi_allocator_done']:
                rows = db.execute('SELECT mapping FROM corpus_functions WHERE symbol=?', (name,)).fetchall()
                self.assertEqual(sum('concrete contextual C-to-ELF statement' in row[0] for row in rows), 1)
            for name, address in [('is_space',29909),('isid',29960),('isnum',30011),('isoct',30044),('toup',30077)]:
                rows = db.execute('SELECT address,mapping FROM corpus_functions WHERE symbol=?', (name,)).fetchall()
                selected = [addr for addr,mapping in rows if 'concrete contextual C-to-ELF statement' in mapping]
                self.assertEqual(selected, [address], name)
            paired = db.execute("SELECT address,mapping FROM corpus_functions WHERE symbol='isid'").fetchall()
            binary_addresses = [addr for addr,mapping in paired if any(s['kind']=='functional_equivalence' for s in json.loads(mapping).get('formal_statements', []))]
            self.assertEqual(sorted(binary_addresses), [24069,29960])
            clones = db.execute("SELECT count(*) FROM corpus_functions WHERE symbol='isnum'").fetchone()[0]
            self.assertGreater(clones, 1, 'same-name local clones remain distinct')
            self.assertGreater(db.execute('SELECT count(*) FROM corpus_functions').fetchone()[0], 42000)
            self.assertGreater(db.execute('SELECT count(*) FROM corpus_timings').fetchone()[0], 10)
            summaries = db.execute('SELECT * FROM corpus_timing_summary ORDER BY run_id').fetchall()
            receipts = db.execute('SELECT * FROM corpus_timings ORDER BY run_id').fetchall()
            self.assertEqual(len(summaries), len(receipts))
            for summary, (run_id, build_id, stage, metadata) in zip(summaries, receipts):
                run = json.loads(metadata)
                self.assertEqual(summary, (run_id, build_id, stage, run.get('wall_seconds'), run.get('peak_rss_kib'), run.get('exit_code')))
            self.assertTrue(all(row[2].upper() != 'BLOB' for row in db.execute('PRAGMA table_info(corpus_artifacts)')))
            db.close()
            again = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/database.py'), '--output', str(output), '--source-rev', '1' * 40], capture_output=True)
            self.assertNotEqual(again.returncode, 0)


if __name__ == '__main__':
    unittest.main()
