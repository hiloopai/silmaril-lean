#!/usr/bin/env python3
"""Independent binary fixtures for checked float bitpatterns and global imports."""
import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--as-command', default='.lake/build/bin/wasm-as')
p.add_argument('--dis-command', default='.lake/build/bin/wasm-dis')
a = p.parse_args()
import shlex
node = shutil.which('node')
if not node:
    raise SystemExit('Node is required for independent execution checks')


def uleb(n):
    bs = bytearray()
    while n >= 128:
        bs.append(n % 128 + 128)
        n //= 128
    bs.append(n)
    return bytes(bs)


def sec(tag, data):
    return bytes([tag]) + uleb(len(data)) + data


def vec(xs):
    return uleb(len(xs)) + b''.join(xs)


def name(s):
    bs = s.encode()
    return uleb(len(bs)) + bs


def run(cmd):
    r = subprocess.run(list(map(str, cmd)), capture_output=True, timeout=90)
    assert r.returncode == 0, (cmd, r.stdout, r.stderr)
    return r


def roundtrip(root, source, stem):
    binary, text, restored = [root / (stem + ext) for ext in ['.wasm', '.wat', '-restored.wasm']]
    binary.write_bytes(source)
    run([*shlex.split(a.dis_command), binary, '-o', text])
    run([*shlex.split(a.as_command), text, '-o', restored])
    assert restored.read_bytes() == source, 'independent canonical fixture lost exact binary content'
    return binary, restored, text


header = b'\x00asm\x01\x00\x00\x00'
f32 = [0, 0x80000000, 1, 0x007fffff, 0x00800000, 0x3f800000, 0x7f7fffff,
       0x7f800000, 0xff800000, 0x7fc00000, 0x7fa00001, 0xffc00001]
f64 = [0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x0010000000000000,
       0x3ff0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000,
       0xfff0000000000000, 0x7ff8000000000000, 0x7ff4000000000001, 0xfff8000000000001]
constants = [(32, bits) for bits in f32] + [(64, bits) for bits in f64]
bodies = [b'\x00' + bytes([0x43 if width == 32 else 0x44]) + bits.to_bytes(width // 8, 'little')
          + bytes([0xbc if width == 32 else 0xbd, 0x0b]) for width, bits in constants]
floats = (header + sec(1, vec([b'\x60\x00\x01\x7f', b'\x60\x00\x01\x7e']))
          + sec(3, vec([uleb(0 if width == 32 else 1) for width, _ in constants]))
          + sec(7, vec([name('b' + str(i)) + b'\x00' + uleb(i) for i in range(len(constants))]))
          + sec(10, vec([uleb(len(body)) + body for body in bodies])))
inc_body = b'\x00\x23\x00\x41\x01\x6a\x24\x00\x23\x00\x0b'
imported = (header + sec(1, vec([b'\x60\x00\x01\x7f']))
            + sec(2, vec([name('env') + name('g') + b'\x03\x7f\x01']))
            + sec(3, b'\x01\x00') + sec(7, b'\x01' + name('inc') + b'\x00\x00')
            + sec(10, b'\x01' + uleb(len(inc_body)) + inc_body))
with tempfile.TemporaryDirectory(prefix='wasm-text-numerics-') as tmp:
    root = Path(tmp)
    before, after, text = roundtrip(root, floats, 'float-bits')
    assert 'nan:0x' in text.read_text() and 'f32.const' in text.read_text() and 'f64.const' in text.read_text()
    run([node, '-e', '''const fs=require('fs');
const expected=JSON.parse(process.argv[3]);
for(const path of [process.argv[1],process.argv[2]]) {
 const i=new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path)));
 expected.forEach(([width,bits],j)=>{
  const actual=BigInt.asUintN(width,BigInt(i.exports['b'+j]()));
  if(actual.toString()!==bits) throw Error(j+': '+actual+' != '+bits);
 });
}''', before, after, json.dumps([(width, str(bits)) for width, bits in constants])])
    before, after, text = roundtrip(root, imported, 'imported-global')
    assert '(import "env" "g" (global (mut i32)))' in text.read_text()
    run([node, '-e', '''const fs=require('fs');
for(const path of [process.argv[1],process.argv[2]]) {
 const g=new WebAssembly.Global({value:'i32',mutable:true},7);
 const i=new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path)),{env:{g}});
 for(const expected of [8,9,10]) if(i.exports.inc()!==expected || g.value!==expected) throw Error('state');
}''', before, after])
print('24 f32/f64 bitpatterns, including signed zero, subnormals, infinities and signed/payload NaNs, roundtrip byte-exactly and execute identically in Node')
print('Imported mutable-global roundtrip retains repeated shared-state writes and reads')
