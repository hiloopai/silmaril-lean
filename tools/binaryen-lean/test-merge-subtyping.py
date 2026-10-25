#!/usr/bin/env python3
"""Check function import covariance/contravariance through the actual merge CLI."""
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

with tempfile.TemporaryDirectory(prefix='merge-function-subtyping-') as temporary:
    root = Path(temporary)
    covariance = (
        '(module (type $super (sub (func (param i32) (result anyref)))) '
        '(type $sub (sub final $super (func (param i32) (result (ref any))))) '
        '(func (export "value") (type $sub) (ref.i31 (local.get 0))))',
        '(module (type $super (sub (func (param i32) (result anyref)))) '
        '(import "Provider" "value" (func $value (type $super))) '
        '(func (export "caller") (result anyref) (call $value (i32.const 42))))',
        'if(i.exports.caller()!==42)process.exit(1);')
    contravariance = (
        '(module (type $super (sub (func (param (ref any)) (result i32)))) '
        '(type $sub (sub final $super (func (param anyref) (result i32)))) '
        '(func (export "value") (type $sub) (i32.const 42)))',
        '(module (type $super (sub (func (param (ref any)) (result i32)))) '
        '(import "Provider" "value" (func $value (type $super))) '
        '(func (export "caller") (result i32) (call $value (ref.i31 (i32.const 7)))))',
        'if(i.exports.caller()!==42)process.exit(1);')
    for label, (provider_source, consumer_source, assertion) in [
            ('covariance', covariance), ('contravariance', contravariance)]:
        provider, consumer = root / (label + '.wat'), root / (label + '.second')
        provider.write_text(provider_source)
        consumer.write_text(consumer_source)
        for binary_inputs in [False, True]:
            inputs = [provider, consumer]
            if binary_inputs:
                inputs = [root / (label + '-provider.wasm'), root / (label + '-consumer.wasm')]
                run([args.reference_as, provider, '--all-features', '-o', inputs[0]])
                run([args.reference_as, consumer, '--all-features', '-o', inputs[1]])
            output = root / (label + '.wasm')
            run([*driver, inputs[0], 'Provider', inputs[1], 'Consumer', '-all', '-o', output])
            run([args.reference_opt, output, '--all-features', '-o', root / 'checked.wasm'])
            run([args.node, '-e', 'const fs=require("fs");const i=new WebAssembly.Instance('
                 'new WebAssembly.Module(fs.readFileSync(process.argv[1])));' + assertion, output])
    # Reversing the variance is unsafe and must not be confused with subtyping.
    provider.write_text(contravariance[0])
    consumer.write_text(contravariance[1].replace('(param (ref any))', '(param anyref)'))
    # The provider's actual type is still nullable here; use the narrower
    # supertype as its exported type to create a genuine incompatible import.
    provider.write_text('(module (type $super (sub (func (param (ref any)) (result i32)))) '
                        '(func (export "value") (type $super) (i32.const 42)))')
    protected = root / 'protected.wasm'
    protected.write_bytes(b'unchanged')
    run([*driver, provider, 'Provider', consumer, 'Consumer', '-all', '-o', protected], 1)
    assert protected.read_bytes() == b'unchanged'
print('PASS: nontrapping return covariance, parameter contravariance, original WAT and binary inputs, independent validation, Node observations and unsafe variance rejection')
