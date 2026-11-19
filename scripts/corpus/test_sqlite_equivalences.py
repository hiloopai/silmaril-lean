"""Actual paired ELF/ABI export and incompatible-build rejection, without rebuilding."""
import copy
import importlib.util
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('binary_view', ROOT/'tools/compiler-explorer/equivalence.py')
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)


class SqliteBinaryEquivalences(unittest.TestCase):
    def setUp(self):
        self.m = json.loads((ROOT/e.MANIFEST).read_text())
        self.endpoints = {x['id']: x for x in self.m['endpoints']}

    def test_actual_seven_pairs_have_distinct_optimization_code_and_bounded_frames(self):
        self.assertEqual(len(self.m['pairs']), 7)
        different = 0
        for p in self.m['pairs']:
            left, right = [self.endpoints[p[k]] for k in ['left', 'right']]
            e.validate_pair(p, left, right)
            a, b = [x['functions'][p['function_symbol']] for x in [left, right]]
            self.assertEqual(e.c.elf_function((ROOT/left['path']).read_bytes(), p['function_symbol'])['bytes_hex'], a['bytes_hex'])
            self.assertEqual(e.c.elf_function((ROOT/right['path']).read_bytes(), p['function_symbol'])['bytes_hex'], b['bytes_hex'])
            different += a['bytes_hex'] != b['bytes_hex']
        self.assertEqual(different, 4)
        self.assertEqual(self.endpoints['smallO2']['functions']['sqlite3_threadsafe']['bytes_hex'], '31 c0 c3')

    def test_differing_version_and_threadsafe_values_are_rejected(self):
        for query, a, b in [('sqlite3_libversion_number','priorO0','defaultO2'),('sqlite3_threadsafe','defaultO2','smallO2')]:
            pair=copy.deepcopy(self.m['pairs'][0]);pair['function_symbol']=query
            with self.assertRaisesRegex(ValueError,'incompatible query'):
                e.validate_pair(pair,self.endpoints[a],self.endpoints[b])
        pair=copy.deepcopy(self.m['pairs'][0]);pair['left_frame']=64
        with self.assertRaisesRegex(ValueError,'private stack'):
            e.validate_pair(pair,self.endpoints[pair['left']],self.endpoints[pair['right']])

    def test_actual_export_retains_unproved_bytes_and_observation_contracts(self):
        with tempfile.TemporaryDirectory() as tmp:
            project=Path(tmp)/'project.sqlite';out=Path(tmp)/'out'
            with sqlite3.connect(project) as db:
                db.executescript('CREATE TABLE corpus_meta(key TEXT,value TEXT); CREATE TABLE corpus_artifacts(id TEXT,path TEXT,sha256 TEXT); CREATE TABLE corpus_functions(artifact TEXT,symbol TEXT,address INTEGER,size INTEGER);')
                db.execute('INSERT INTO corpus_meta VALUES(?,?)',('revision','a'*40))
                for endpoint in [x for name in e.MANIFESTS for x in json.loads((ROOT/name).read_text())['endpoints']]:
                    db.execute('INSERT INTO corpus_artifacts VALUES(?,?,?)',(endpoint['id'],endpoint['path'],endpoint['sha256']))
                    for symbol,f in endpoint['functions'].items():
                        db.execute('INSERT INTO corpus_functions VALUES(?,?,?,?)',(endpoint['id'],symbol,f['address'],f['size']))
            rows=e.export(project,out)
            self.assertEqual(len(rows),16)
            registry=json.loads((ROOT/e.c.REGISTRY).read_text())['statements']
            self.assertEqual(sum(x['kind']=='functional_equivalence' for x in registry),16)
            self.assertEqual(sum(x['kind']=='functional_equivalence' and x.get('viewer_kind')!='binary_equivalence' for x in registry),0)
            for row in rows:
                p=json.loads((out/Path(row['static_path']).name).read_text())
                self.assertEqual(p['status'],'UNPROVED');self.assertFalse(p['source_refinement_assumed'])
                self.assertIsNone(p['proof_evidence']);self.assertIsNone(p['exporter_run'])
                self.assertEqual([a['role'] for a in p['artifacts']],['left','right'])
                self.assertEqual(len(p['modules']),10 if p['pair'].get('profile','').startswith('legacy-') else 6 if p['pair'].get('profile')=='cjson-interior-detach-v1' else 4)
            for endpoint in json.loads((ROOT/e.MANIFESTS[1]).read_text())['endpoints']:
                with sqlite3.connect(project) as db:db.execute('UPDATE corpus_functions SET address=0 WHERE artifact=?',(endpoint['id'],))
                with self.assertRaisesRegex(ValueError,'function mismatch'):e.export(project,out)
                with sqlite3.connect(project) as db:db.execute('UPDATE corpus_functions SET address=? WHERE artifact=?',(endpoint['functions']['cJSON_GetArraySize']['address'],endpoint['id']))
            with sqlite3.connect(project) as db:db.execute('UPDATE corpus_functions SET address=0')
            with self.assertRaisesRegex(ValueError,'function mismatch'):e.export(project,out)


if __name__=='__main__':unittest.main()
