"""Export measured binary problems as two real ELF endpoints, never C/Core fixtures."""
import importlib.util
import json
from pathlib import Path
import re
import sqlite3

_spec = importlib.util.spec_from_file_location('binary_corpus', Path(__file__).with_name('corpus.py'))
c = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(c)
MANIFEST = 'corpus/sqlite/equivalence/build-queries/manifest.json'
MANIFESTS = [MANIFEST, 'corpus/cjson/equivalence/array-size/manifest.json', 'corpus/cjson/equivalence/detach/manifest.json', 'corpus/legacy/equivalence/manifest.json', 'corpus/darkhttpd/equivalence/logencoding/manifest.json']


def validate_pair(pair, left, right):
    """Reject incompatible observed queries; this does not prove machine semantics."""
    if pair.get('profile') == 'darkhttpd-byte-predicate-v1':
        if pair['function_symbol'] != 'needs_logencoding' or pair.get('value') is not None:
            raise ValueError('invalid byte-predicate observation')
        if pair['left_frame'] != 12 or pair['right_frame'] != 0:
            raise ValueError('unexpected byte-predicate frame')
        for key in ['source_sha256', 'project', 'version', 'configuration', 'target', 'source_inputs']:
            if left['build'][key] != right['build'][key]:
                raise ValueError('incompatible byte-predicate build pair')
        if left['source'] != right['source']:
            raise ValueError('incompatible byte-predicate source')
        if left['build']['optimization'] != 'O0' or right['build']['optimization'] != 'Og':
            raise ValueError('invalid byte-predicate optimization pair')
        return
    if pair.get('profile') in ['legacy-mimalloc-version-v1', 'legacy-tinycc-isid-v1']:
        version = pair['profile'] == 'legacy-mimalloc-version-v1'
        if pair['function_symbol'] != ('mi_version' if version else 'isid') or pair['value'] != (219 if version else None):
            raise ValueError('invalid legacy contract meaning')
        if pair['left_frame'] != (8 if version else 16) or pair['right_frame'] != (8 if version else 16):
            raise ValueError('changed original legacy contract frame')
        for key in ['configuration', 'version', 'project', 'target', 'source_inputs']:
            if left['build'][key] != right['build'][key]:
                raise ValueError('incompatible legacy build pair')
        if left['source'] != right['source']:
            raise ValueError('incompatible legacy included source')
        return
    if pair.get('profile') == 'cjson-interior-detach-v1':
        if pair['function_symbol'] != 'cJSON_DetachItemViaPointer' or pair.get('value') is not None:
            raise ValueError('invalid detachment observation')
        if pair['left_frame'] != 24 or pair['right_frame'] != 0 or pair['object_count'] != 5:
            raise ValueError('unexpected detachment frame/domain')
        for key in ['source_sha256', 'version', 'configuration', 'target']:
            if left['build'][key] != right['build'][key]:
                raise ValueError('incompatible detachment source/configuration')
        if left['build']['optimization'] != 'O0' or right['build']['optimization'] != 'O2':
            raise ValueError('invalid detachment optimization pair')
        return
    if pair.get('profile') == 'cjson-finite-list-v1':
        if pair['function_symbol'] != 'cJSON_GetArraySize' or pair.get('value') is not None:
            raise ValueError('invalid traversal observation')
        if pair['left_frame'] != 32 or pair['right_frame'] != 0 or pair['length_bound'] != 64:
            raise ValueError('unexpected traversal frame/domain')
        for key in ['source_sha256', 'version', 'configuration', 'target']:
            if left['build'][key] != right['build'][key]:
                raise ValueError('incompatible traversal source/configuration')
        if left['build']['optimization'] != 'O0' or right['build']['optimization'] != 'O2':
            raise ValueError('invalid traversal optimization pair')
        return
    key = 'version_number' if pair['function_symbol'] == 'sqlite3_libversion_number' else 'threadsafe_setting'
    if pair['function_symbol'] not in ['sqlite3_libversion_number', 'sqlite3_threadsafe']:
        raise ValueError('unsupported binary query')
    if left[key] != right[key] or pair['value'] != left[key]:
        raise ValueError('incompatible query results; not selected for equivalence')
    for role, endpoint in [('left', left), ('right', right)]:
        frame = 8 if endpoint['build']['optimization'] == 'O0' else 0
        if pair[role + '_frame'] != frame:
            raise ValueError('unexpected private stack frame')


def validate_cjson_build(root, endpoint):
    """Check normalized display fields against real, differently shaped old receipts."""
    receipt = json.loads(c.public_file(root, endpoint['receipt']['path']).read_bytes())
    build = endpoint['build']
    if receipt['package'] != 'cjson' or receipt['version'] != build['version'] or receipt['arch'] != 'x86_64':
        raise ValueError('traversal receipt identity mismatch')
    if any(receipt[k] != build[k] for k in ['cflags', 'configure_args', 'compiler']):
        raise ValueError('traversal build fields mismatch')
    if receipt['image']['id'] != build['image_id'] or build['source_inputs'] != receipt['inputs']:
        raise ValueError('traversal build image/source mismatch')
    if build['source_sha256'] != endpoint['source']['sha256'] or build['configuration'] != 'default' or build['target'] != 'x86_64-linux-gnu':
        raise ValueError('traversal source/configuration mismatch')
    if not re.search(r'(?:^| )-O'+build['optimization'][1:]+r'(?: |$)', receipt['cflags']):
        raise ValueError('traversal optimization mismatch')
    outputs = [x for x in receipt['outputs'] if x['object'] == 'libcjson.so.1']
    if len(outputs) != 1 or outputs[0]['sha256'] != endpoint['sha256']:
        raise ValueError('traversal receipt artifact mismatch')
    if endpoint['id'] == 'O0':
        actual = json.loads(c.public_file(root, build['path']).read_bytes())
        for key in ['configuration', 'version', 'optimization', 'image_id', 'source_inputs', 'target']:
            if build[key] != actual[key]:
                raise ValueError('traversal variant build mismatch')
        if not any(x['path'] == endpoint['source']['path'] and x['sha256'] == endpoint['source']['sha256'] for x in actual['included_source_files']):
            raise ValueError('traversal included source mismatch')
    elif endpoint['id'] != 'O2' or build['path'] != endpoint['receipt']['path']:
        raise ValueError('traversal canonical receipt mismatch')


def validate_darkhttpd_build(root, endpoint):
    """Validate display identity against the actual variant build and receipt."""
    receipt = json.loads(c.public_file(root, endpoint['receipt']['path']).read_bytes())
    build = endpoint['build']
    actual = json.loads(c.public_file(root, build['path']).read_bytes())
    if build['project'] != 'darkhttpd' or build['configuration'] != 'default' or build['target'] != 'x86_64-linux-gnu':
        raise ValueError('byte-predicate project/configuration/target mismatch')
    for key in ['project', 'version', 'configuration', 'target', 'optimization', 'image_id', 'source_inputs']:
        if actual[key] != build[key]:
            raise ValueError('byte-predicate build identity mismatch')
    if receipt['package'] != build['project'] or receipt['version'] != build['version'] or receipt['arch'] != 'x86_64':
        raise ValueError('byte-predicate receipt identity mismatch')
    if any(receipt[k] != build[k] for k in ['compiler', 'cflags', 'configure_args']):
        raise ValueError('byte-predicate receipt fields mismatch')
    if receipt['image']['id'] != build['image_id'] or receipt['inputs'] != build['source_inputs']:
        raise ValueError('byte-predicate receipt image/source mismatch')
    if not re.search(r'(?:^| )-'+build['optimization']+r'(?: |$)', receipt['cflags']):
        raise ValueError('byte-predicate receipt optimization mismatch')
    if build['source_sha256'] != endpoint['source']['sha256'] or not any(
            x['path'] == endpoint['source']['path'] and x['sha256'] == endpoint['source']['sha256']
            for x in actual['included_source_files']):
        raise ValueError('byte-predicate included source mismatch')
    outputs = [x for x in receipt['outputs'] if x['object'] == 'darkhttpd']
    if len(outputs) != 1 or outputs[0]['path'] != endpoint['path'] or outputs[0]['sha256'] != endpoint['sha256']:
        raise ValueError('byte-predicate receipt artifact mismatch')


def export(project, output, root=c.ROOT):
    registry_data = c.public_file(root, c.REGISTRY).read_bytes()
    statements = [s for s in json.loads(registry_data)['statements'] if s.get('viewer_kind') == 'binary_equivalence']
    output.mkdir(parents=True, exist_ok=True)
    (output / 'blobs').mkdir(exist_ok=True)
    if not statements:
        (output / 'index.json').write_text('[]\n')
        return []
    pairs = {}
    for name in MANIFESTS:
        raw = c.public_file(root, name).read_bytes()
        m = json.loads(raw)
        if m['schema'] != 'silmaril.binary-equivalence.v1':
            raise ValueError('unsupported binary manifest')
        endpoints = {e['id']: e for e in m['endpoints']}
        for pair in m['pairs']:
            if pair['declaration'] in pairs:
                raise ValueError('duplicate binary manifest declaration')
            pairs[pair['declaration']] = (pair, endpoints, m, name, raw)
    if set(pairs) != {s['declaration'] for s in statements}:
        raise ValueError('binary registry/manifest mismatch')
    listing = []
    with sqlite3.connect(project.resolve().as_uri() + '?mode=ro', uri=True) as db:
        db.row_factory = sqlite3.Row
        revision = db.execute("SELECT value FROM corpus_meta WHERE key='revision'").fetchone()[0]
        if not re.fullmatch('[0-9a-f]{40}', revision):
            raise ValueError('missing immutable public revision')
        for s in statements:
            if s['kind'] != 'functional_equivalence' or s['status'] != 'stated-unproved':
                raise ValueError('unexpected binary problem status')
            pair, endpoints, manifest, manifest_path, data = pairs[s['declaration']]
            pins = {**s['artifact_sha256'], **s['module_sha256']}
            for name, digest in pins.items():
                if c.sha(c.public_file(root, name).read_bytes()) != digest:
                    raise ValueError('stale binary evidence: ' + name)
            if pins.get(manifest_path) != c.sha(data):
                raise ValueError('unpinned binary manifest')
            validate_pair(pair, endpoints[pair['left']], endpoints[pair['right']])
            artifacts = []
            for role in ['left', 'right']:
                e = endpoints[pair[role]]
                for evidence in [e['source'], e['receipt'], e['build']]:
                    raw = c.public_file(root, evidence['path']).read_bytes()
                    if pins.get(evidence['path']) != c.sha(raw) or evidence['sha256'] != c.sha(raw):
                        raise ValueError('stale binary build/source receipt')
                if pair.get('profile') == 'darkhttpd-byte-predicate-v1':
                    validate_darkhttpd_build(root, e)
                    raw_source = c.public_file(root, e['source']['path']).read_bytes()
                elif pair.get('profile') in ['cjson-finite-list-v1', 'cjson-interior-detach-v1']:
                    validate_cjson_build(root, e)
                    raw_source = c.public_file(root, e['source']['path']).read_bytes()
                elif pair.get('profile') in ['legacy-mimalloc-version-v1', 'legacy-tinycc-isid-v1']:
                    receipt = json.loads(c.public_file(root, e['receipt']['path']).read_bytes())
                    build = json.loads(c.public_file(root, e['build']['path']).read_bytes())
                    for key in ['configuration', 'version', 'optimization', 'image_id', 'source_inputs', 'project', 'target']:
                        if e['build'][key] != build[key]:
                            raise ValueError('legacy build fields mismatch')
                    if receipt['cflags'] != e['build']['cflags'] or receipt['image']['id'] != build['image_id']:
                        raise ValueError('legacy receipt flags/image mismatch')
                    if receipt['package'] != build['project'] or receipt['version'] != build['version']:
                        raise ValueError('legacy receipt package/version mismatch')
                    if not any(x['path'] == e['source']['path'] and x['sha256'] == e['source']['sha256'] for x in build['included_source_files']):
                        raise ValueError('legacy included-source identity mismatch')
                    if not any(x['sha256'] == e['sha256'] for x in receipt['outputs']):
                        raise ValueError('legacy receipt artifact mismatch')
                    raw_source = c.public_file(root, e['source']['path']).read_bytes()
                else:
                    actual_receipt = json.loads(c.public_file(root, e['receipt']['path']).read_bytes())
                    actual_build = json.loads(c.public_file(root, e['build']['path']).read_bytes())
                    if any(e['build'][key] != actual_build[key] for key in ['configuration', 'version', 'optimization', 'image_id', 'source_inputs']):
                        raise ValueError('binary build fields mismatch')
                    if e['build']['cflags'] != actual_receipt['cflags'] or e['source']['path'] not in {x['path'] for x in actual_build['included_source_files']}:
                        raise ValueError('binary build/source correspondence mismatch')
                    setting = re.search(r'-DSQLITE_THREADSAFE=(\d)', actual_receipt['cflags'])
                    if not setting or int(setting[1]) != e['threadsafe_setting']:
                        raise ValueError('binary THREADSAFE option mismatch')
                    raw_source = c.public_file(root, e['source']['path']).read_bytes()
                    version = re.search(rb'#define SQLITE_VERSION_NUMBER\s+(\d+)', raw_source)
                    if not version or int(version[1]) != e['version_number']:
                        raise ValueError('binary source version mismatch')
                span = e['source']['definitions'][pair['function_symbol']]
                excerpt = raw_source[span['offset']:span['offset']+span['length']]
                if c.sha(excerpt) != span['sha256'] or excerpt.decode() != span['text']:
                    raise ValueError('binary source definition span mismatch')
                row = db.execute('SELECT id,sha256 FROM corpus_artifacts WHERE path=?', (e['path'],)).fetchone()
                if row is None or row['sha256'] != pins.get(e['path']) or row['sha256'] != e['sha256']:
                    raise ValueError('binary catalog artifact mismatch')
                actual = c.elf_function(c.public_file(root, e['path']).read_bytes(), pair['function_symbol'], e['functions'][pair['function_symbol']]['address'])
                if any(actual[k] != e['functions'][pair['function_symbol']][k] for k in actual):
                    raise ValueError('binary function identity mismatch')
                if not db.execute('SELECT count(*) FROM corpus_functions WHERE artifact=? AND symbol=? AND address=? AND size=?',
                        (row['id'], pair['function_symbol'], actual['address'], actual['size'])).fetchone()[0]:
                    raise ValueError('binary catalog function mismatch')
                artifacts.append(dict(role=role, id=row['id'], path=e['path'], sha256=e['sha256'], frame=pair[role+'_frame'], build=e['build'], receipt=e['receipt'], source=e['source'], **actual))
            run = json.loads(c.public_file(root, s['run_receipt']).read_bytes())
            if run['exit_code'] != 0 or s['root'] not in run['command']:
                raise ValueError('binary measured check mismatch')
            modules = []
            for name in manifest.get('context_modules', [manifest['definition'], s['root'].replace('.', '/') + '.lean', 'Silmaril/Project/Shapes/SysV/Defs.lean', 'Silmaril/Project/Shapes/X86/Defs.lean']):
                raw = c.public_file(root, name).read_bytes()
                if pins.get(name) != c.sha(raw) or len(raw) > c.MAX_TEXT:
                    raise ValueError('unpinned or excessive binary context')
                digest = c.sha(raw)
                (output / 'blobs' / (digest + '.txt')).write_bytes(raw)
                modules.append(dict(path=name,sha256=digest,size=len(raw),static_path='api/equivalences/blobs/'+digest+'.txt'))
            payload = dict(schema='silmaril.binary-view.v1', declaration=s['declaration'], function_symbol=pair['function_symbol'], root=s['root'],
                status='UNPROVED', kind='functional_equivalence', revision=revision, artifacts=artifacts, modules=modules, pair=pair,
                excluded=manifest['excluded'], limits=manifest['limits'], run_receipt=s['run_receipt'], proof_evidence=None, exporter_run=None,
                interactive_compilation=False, source_refinement_assumed=False, manifest=dict(path=manifest_path,sha256=c.sha(data)),
                registry=dict(path=c.REGISTRY,sha256=c.sha(registry_data)))
            key=c.sha(s['declaration'].encode())
            (output/(key+'.json')).write_text(json.dumps(payload,indent=2)+'\n')
            listing.append(dict(declaration=s['declaration'],function_symbol=pair['function_symbol'],status='UNPROVED',static_path='api/equivalences/'+key+'.json'))
    (output/'index.json').write_text(json.dumps(listing,indent=2)+'\n')
    return listing
