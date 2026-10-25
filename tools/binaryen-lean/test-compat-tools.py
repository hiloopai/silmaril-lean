#!/usr/bin/env python3
"""Real-file tests for the explicit Binaryen CLI compatibility subset."""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bin-dir', type=Path, default=Path('.lake/build/bin'))
parser.add_argument('--lean', help='Use LEAN --run instead of native binaries')
a = parser.parse_args()
source_root = Path(__file__).resolve().parents[2]
entries = {'as': 'As', 'dis': 'Dis', 'merge': 'Merge', 'shell': 'Shell',
           'ctor-eval': 'CtorEval', 'metadce': 'MetaDCE'}


def call(tool, *args, input=None, cwd=None):
    driver = ([a.lean, '--run', str(source_root / 'tools/binaryen-lean' /
                                  f'Wasm{entries[tool]}Compat.lean')] if a.lean else
              [str(a.bin_dir.resolve() / f'wasm-{tool}')])
    return subprocess.run([*driver, *map(str, args)], input=input,
                          capture_output=True, cwd=cwd, timeout=90)


def ok(tool, *args, **kwargs):
    r = call(tool, *args, **kwargs)
    assert r.returncode == 0, (tool, args, r.stdout, r.stderr)
    return r


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def name(s):
    return bytes([len(s)]) + s.encode()


def module(export, value, imported=None):
    imports = b'' if imported is None else section(2, b'\x01' + name(imported[0]) + name(imported[1]) + b'\x00\x00')
    index = 0 if imported is None else 1
    code = b'\x00\x41' + bytes([value]) + b'\x0b' if imported is None else b'\x00\x10\x00\x0b'
    return (b'\x00asm\x01\x00\x00\x00' + section(1, b'\x01\x60\x00\x01\x7f') + imports
            + section(3, b'\x01\x00') + section(7, b'\x01' + name(export) + bytes([0, index]))
            + section(10, b'\x01' + bytes([len(code)]) + code))


def constructor():
    bodies = [bytes([0, 0x41, 9, 0x24, 0, 0x0B]), bytes([0, 0x23, 0, 0x0B])]
    return (b'\x00asm\x01\x00\x00\x00'
            + section(1, bytes([2, 0x60, 0, 0, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([2, 0, 1]))
            + section(6, bytes([1, 0x7F, 1, 0x41, 3, 0x0B]))
            + section(7, bytes([2]) + name('get') + bytes([0, 1]) + name('state') + bytes([3, 0]))
            + section(8, bytes([0]))
            + section(10, bytes([2]) + b''.join(bytes([len(b)]) + b for b in bodies)))


for tool in entries:
    assert b'usage: wasm-' in ok(tool, '-h').stdout
    assert b'Silmaril' in ok(tool, '--version').stdout

with tempfile.TemporaryDirectory(prefix='binaryen-compat-') as tmp:
    root = Path(tmp)
    wat = root / 'sample.wat'
    wat.write_text((source_root / 'tools/binaryen-lean/text-tools/integer-locals.wat').read_text())
    ok('as', wat)
    binary = wat.with_suffix('.wasm')
    assert binary.is_file()
    assert ok('shell', '--invoke', 'run', binary, '20', '--fuel', '100').stdout.strip() == b'return [i32:42]'
    text = ok('dis', binary).stdout
    assert text.startswith(b'(module')
    encoded = ok('as', '--output=-', '-', input=text)
    assert encoded.stdout == binary.read_bytes()
    assert ok('dis', '-', input=encoded.stdout).stdout == text
    printed = root / 'printed.wat'
    ok('dis', '--output', printed, binary)
    assert printed.read_bytes() == text
    rebuilt = root / 'rebuilt.wasm'
    ok('as', '-o', rebuilt, '--', printed)
    assert rebuilt.read_bytes() == binary.read_bytes()

    provider, consumer, merged = [root / (s + '.wasm') for s in ['provider', 'consumer', 'merged']]
    provider.write_bytes(module('a', 42))
    consumer.write_bytes(module('b', 0, ('A', 'a')))
    ok('merge', provider, 'A', '--output=' + str(merged), consumer, 'B')
    assert ok('shell', '--fuel', '100', merged, '--invoke', 'b').stdout.strip() == b'return [i32:42]'
    ok('merge', provider, 'A', consumer, 'B')  # upstream's no-output check mode
    assert call('merge', consumer, 'B', provider, 'A', '-o', merged).returncode == 1

    ctor_input, ctor_output = root / 'constructor.wasm', root / 'initialized.wasm'
    ctor_input.write_bytes(constructor())
    ok('ctor-eval', ctor_input)  # check/evaluate without output
    ok('ctor-eval', '--output', ctor_output, ctor_input)
    assert ok('ctor-eval', ctor_input, '--output=-').stdout == ctor_output.read_bytes()
    assert ok('shell', '--fuel', '100', '--invoke', 'get', ctor_output).stdout.strip() == b'return [i32:9]'

    graph, trimmed = root / 'graph.json', root / 'trimmed.wasm'
    graph.write_text(json.dumps([{'name': 'api', 'root': True, 'export': 'a'}]))
    result = ok('metadce', '--output=' + str(trimmed), '--graph-file', graph, provider)
    assert b'applied checked' in result.stderr
    assert ok('shell', '--fuel', '100', '--invoke', 'a', trimmed).stdout.strip() == b'return [i32:42]'
    ok('metadce', provider, '--graph-file=' + str(graph))
    assert ok('metadce', '-', '--graph-file', graph, '--output=-',
              input=provider.read_bytes()).stdout == trimmed.read_bytes()
    graph.write_text('[]')
    result = ok('metadce', '--graph-file', graph, ctor_input, '-o', trimmed)
    assert b'skipped' in result.stderr and trimmed.read_bytes() == ctor_input.read_bytes()
    assert call('metadce', provider, '--graph-file', graph, '--graph-file', graph).returncode == 2
    assert call('metadce', '-', '--graph-file=-').returncode == 2

    sentinel = b'output must survive rejection'
    for tool, base, flag in [('as', [wat], '--debuginfo'), ('dis', [binary], '--source-map'),
                             ('merge', [provider, 'A'], '--output-manifest=unused.manifest'),
                             ('ctor-eval', [binary], '--ctors')]:
        rebuilt.write_bytes(sentinel)
        rejected = call(tool, *base, '-o', rebuilt, flag)
        assert rejected.returncode == 2 and b'unsupported option' in rejected.stderr
        assert rebuilt.read_bytes() == sentinel
        assert call(tool, *base, '-o', rebuilt, '--output', 'duplicate').returncode == 2
        assert rebuilt.read_bytes() == sentinel
    assert call('shell', wat).returncode == 2
    assert call('shell', '--fuel', '0', '--invoke', 'run', binary, '20').returncode == 3

print('Upstream-named CLI shape, output defaults/stdin/stdout, merge FILE NAME, shell extension and rejection preservation pass')
