#!/usr/bin/env python3
"""Check automatic finite silent starts and original WAT/-S CLI processing."""
import argparse
import shlex
import subprocess
import tempfile
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--driver', required=True)
parser.add_argument('--reference-as', default='wasm-as')
parser.add_argument('--reference-opt', default='wasm-opt')
parser.add_argument('--node', default='node')
args = parser.parse_args()
driver = shlex.split(args.driver)

def run(command, expected=0):
    result = subprocess.run(list(map(str, command)), capture_output=True, timeout=60)
    assert result.returncode == expected, (command, result.returncode, result.stdout, result.stderr)
    return result

with tempfile.TemporaryDirectory(prefix='merge-supported-') as temporary:
    root = Path(temporary)
    # Deliberately arbitrary extensions, matching upstream's .second convention.
    first, second = root / 'provider.wat', root / 'consumer.second'
    first.write_text('(module (func $start (drop (i32.const 9))) (start $start) '
                     '(func (export "run") (result i32) (i32.const 11)))')
    second.write_text('(module (import "A" "run" (func $run (result i32))) '
                      '(func (export "via") (result i32) '
                      '(i32.add (call $run) (i32.const 31))))')
    sources = [(first, second)]
    binary_first, binary_second = root / 'first.wasm', root / 'second.wasm'
    run([args.reference_as, first, '-o', binary_first])
    run([args.reference_as, second, '-o', binary_second])
    sources.append((binary_first, binary_second))
    for provider, consumer in sources:
        for text in [False, True]:
            output = root / ('out.wat' if text else 'out.wasm')
            flags = ['-S'] if text else []
            run([*driver, '-all', provider, 'A', consumer, 'B',
                 '--rename-export-conflicts', *flags, '-o', output])
            binary = output
            if text:
                binary = root / 'assembled.wasm'
                run([args.reference_as, output, '--all-features', '-o', binary])
            run([args.reference_opt, binary, '--all-features', '-o', root / 'checked.wasm'])
            run([args.node, '-e', 'const fs=require("fs");const i=new WebAssembly.Instance('
                 'new WebAssembly.Module(fs.readFileSync(process.argv[1])));'
                 'if(i.exports.run()!==11||i.exports.via()!==42)process.exit(1);', binary])
    stdout = run([*driver, first, 'A', second, 'B', '-S', '-o', '-']).stdout
    (root / 'stdout.wat').write_bytes(stdout)
    run([args.reference_as, root / 'stdout.wat', '-o', root / 'stdout.wasm'])
    empty_source, identity_source = root / 'empty.wat', root / 'identity.wat'
    empty_source.write_text('(module)')
    identity_source.write_text('(module (memory (export "memory") 1) '
        '(global $g (mut i32) (i32.const 0)) '
        '(func $start (global.set $g (i32.const 42))) (start $start) '
        '(func (export "read") (result i32) (global.get $g)))')
    empty_binary, identity_binary = root / 'empty.wasm', root / 'identity.wasm'
    run([args.reference_as, empty_source, '-o', empty_binary])
    run([args.reference_as, identity_source, '-o', identity_binary])
    for left, right in [(empty_binary, identity_binary), (identity_binary, empty_binary)]:
        output = root / 'identity-output.wasm'
        run([*driver, left, 'Left', right, 'Right', '-o', output])
        assert output.read_bytes() == identity_binary.read_bytes()
        run([args.node, '-e', 'const fs=require("fs");const i=new WebAssembly.Instance('
             'new WebAssembly.Module(fs.readFileSync(process.argv[1])));'
             'if(i.exports.read()!==42||i.exports.memory.buffer.byteLength!==65536)process.exit(1);', output])
    # The certified alias scope handles independent closed function modules.
    # The original provider also exercises composition with silent-start erasure.
    alias_b, alias_c = root / 'aliases.second', root / 'aliases.third'
    alias_b.write_text('(module (func (export "run") (result i32) (i32.const 42)))')
    alias_c.write_text('(module (func (export "run_1") (result i32) (i32.const 99)))')
    for policy, expected in [('--rename-export-conflicts', '["run","run_1","run_2"]'),
                             ('--skip-export-conflicts', '["run","run_1"]')]:
        alias_output = root / 'aliases.wasm'
        run([*driver, first, 'A', alias_b, 'B', alias_c, 'C', policy, '-o', alias_output])
        run([args.reference_opt, alias_output, '--all-features', '-o', root / 'checked.wasm'])
        run([args.node, '-e', 'const fs=require("fs");const i=new WebAssembly.Instance('
             'new WebAssembly.Module(fs.readFileSync(process.argv[1])));'
             'if(JSON.stringify(Object.keys(i.exports).sort())!==process.argv[2])process.exit(1);'
             'if(i.exports.run()!==11||i.exports.run_1()!==99)process.exit(2);'
             'if(i.exports.run_2&&i.exports.run_2()!==42)process.exit(3);', alias_output, expected])
    protected = root / 'protected.wasm'
    for flags, expected in [(['--nonexistent'], 2), (['-g'], 2),
                            (['--rename-export-conflicts', '--skip-export-conflicts'], 2),
                            (['-S', '--emit-text'], 2)]:
        protected.write_bytes(b'unchanged')
        run([*driver, first, 'A', second, 'B', *flags, '-o', protected], expected)
        assert protected.read_bytes() == b'unchanged'
    first.write_text('(module (func $start unreachable) (start $start))')
    protected.write_bytes(b'unchanged')
    run([*driver, first, 'A', second, 'B', '-o', protected], 1)
    assert protected.read_bytes() == b'unchanged'
print('PASS: original WAT/.second and binary, automatic silent starts, certified rename/skip policies, checked -S/stdout, Node observations and protected outputs')
