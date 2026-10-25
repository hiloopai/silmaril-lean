#!/usr/bin/env python3
"""Integer-global real-file round trips and independent wire/Node checks."""

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def leb(value):
    result = bytearray()
    while value >= 128:
        result.append(value % 128 + 128)
        value //= 128
    result.append(value)
    return bytes(result)


def section(tag, payload):
    return bytes([tag]) + leb(len(payload)) + payload


def name(text):
    data = text.encode("utf-8")
    return leb(len(data)) + data


arguments = sys.argv[1:]
if arguments and arguments[0] == "--as-driver":
    split = arguments.index("--dis-driver")
    commands = {"as": arguments[1:split], "dis": arguments[split + 1:]}
    assert commands["as"] and commands["dis"]
else:
    driver = arguments or [".lake/build/bin/binaryen-tools-lean"]
    commands = {command: [*driver, command] for command in ["as", "dis"]}

node = shutil.which("node")
header = b"\x00asm\x01\x00\x00\x00"
bodies = [bytes([0, 0x23, 1, 0x20, 0, 0x6A, 0x24, 1, 0x23, 1, 0x0B]),
          bytes([0, 0x23, 0, 0x0B]), bytes([0, 0x23, 2, 0x0B])]
exports = [("bump", 0, 0), ("answer", 0, 1), ("wide", 0, 2),
           ("initial", 3, 0), ("counter", 3, 1), ("big", 3, 2), ("memory", 2, 0)]
# Independent wire construction: i32 immutable 42, i32 mutable -1, i64 immutable -1.
reference = (header
             + section(1, bytes([3, 0x60, 1, 0x7F, 1, 0x7F,
                                0x60, 0, 1, 0x7F, 0x60, 0, 1, 0x7E]))
             + section(3, bytes([3, 0, 1, 2])) + section(5, bytes([1, 0, 1]))
             + section(6, bytes([3, 0x7F, 0, 0x41, 42, 0x0B,
                                0x7F, 1, 0x41, 0x7F, 0x0B,
                                0x7E, 0, 0x42, 0x7F, 0x0B]))
             + section(7, leb(len(exports)) + b"".join(
                 name(text) + bytes([kind]) + leb(index) for text, kind, index in exports))
             + section(10, leb(len(bodies)) + b"".join(leb(len(body)) + body for body in bodies)))

with tempfile.TemporaryDirectory(prefix="wasm-text-globals-") as tmp:
    root = Path(tmp)
    wat, binary, printed, rebuilt = (root / item for item in
                                    ["input.wat", "input.wasm", "printed.wat", "rebuilt.wasm"])
    wat.write_text((Path(__file__).resolve().parent / "text-tools" / "globals.wat").read_text())

    def call(command, source, target):
        return subprocess.run([*commands[command], str(source), "-o", str(target)],
                              text=True, capture_output=True, check=False)

    def execute(path):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
if (e.answer() !== 42 || e.initial.value !== 42 || e.counter.value !== -1 ||
    e.wide() !== -1n || e.big.value !== -1n || e.memory.buffer.byteLength !== 65536)
  process.exit(1);
if (e.bump(43) !== 42 || e.counter.value !== 42) process.exit(1);
e.counter.value = 2147483647;
if (e.bump(1) !== -2147483648 || e.counter.value !== -2147483648 ||
    e.bump(-1) !== 2147483647) process.exit(1);
for (const [global, value] of [[e.initial, 0], [e.big, 0n]]) {
  let rejected = false;
  try { global.value = value; } catch (error) {
    if (!(error instanceof TypeError)) throw error;
    rejected = true;
  }
  if (!rejected) process.exit(1);
}
""", str(path)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute(binary)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert "(global (mut i32) i32.const 4294967295)" in printed.read_text()
    assert "(global i64 i64.const 18446744073709551615)" in printed.read_text()
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute(rebuilt)

    binary.write_bytes(reference)
    execute(binary)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute(rebuilt)
    print("Integer-global text/binary round trips passed, including independent wire bytes")
    print("Node checked exported globals, mutation, wrapping, i64 and immutability" if node else
          "Node unavailable; independent execution checks skipped")

    wat.write_text('(module (type (func (param) (result i32))) '
                   '(import "env" "f" (func (type 0))) (memory 1) '
                   '(global i32 i32.const 42) '
                   '(func (type 0) (local) call 0 global.get 0 i32.add) '
                   '(export "run" (func 1)) (export "memory" (memory 0)))')
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    if node:
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])),
  {env: {f: () => 42}}).exports;
if (e.run() !== 84 || e.memory.buffer.byteLength !== 65536) process.exit(1);
""", str(binary)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr
    print("Globals compose with the existing function-import and memory index spaces")

    sentinel = b"preserve existing output"
    for text in ['(module (global f32 f32.const 0))',
                 '(module (global i32 i32.const 0 i32.const 1 i32.add))',
                 '(module (global i32 (i32.const 0)))', '(module (global i32 i32.const 00))',
                 '(module (global i32 i32.const 0) (memory 1))']:
        wat.write_text(text)
        result = call("as", wat, binary)
        assert result.returncode == 0, (text, result.stderr)
        result = call("dis", binary, printed)
        assert result.returncode == 0, result.stderr
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, result.stderr
        assert binary.read_bytes() == rebuilt.read_bytes()
    for text in ['(module (global i32 i64.const 0))',
                 '(module (global i32))', '(module (global i32 i32.const 0 i32.const 1))',
                 '(module (global i32 i32.const 0) (export "x" (global 1)))',
                 '(module (type (func (param) (result))) (global i32 i32.const 0) '
                 '(func (type 0) (local) i32.const 1 global.set 0))']:
        wat.write_text(text)
        binary.write_bytes(sentinel)
        result = call("as", wat, binary)
        assert result.returncode == 1, (text, result.returncode, result.stderr)
        assert binary.read_bytes() == sentinel
    # These former surface boundaries are now accepted without weakening the contract.
    for supported in [header + section(6, bytes([1, 0x7D, 0, 0x43, 0, 0, 0, 0, 0x0B])),
                      header + section(6, bytes([1, 0x7F, 0, 0x41, 0, 0x41, 1, 0x6A, 0x0B])),
                      header + section(2, bytes([1]) + name("env") + name("g")
                                       + bytes([3, 0x7F, 0]))]:
        binary.write_bytes(supported)
        result = call("dis", binary, printed)
        assert result.returncode == 0, result.stderr
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, result.stderr
        assert rebuilt.read_bytes() == supported
    # Reference-valued globals now have certified rendering and source checking.
    for supported in [header + section(6, bytes([1, 0x70, 0, 0xD0, 0x70, 0x0B])),
                        header + section(2, bytes([1]) + name("env") + name("g")
                                         + bytes([3, 0x70, 0]))]:
        binary.write_bytes(supported)
        result = call("dis", binary, printed)
        assert result.returncode == 0, result.stderr
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, result.stderr
        assert rebuilt.read_bytes() == supported
    print("Extended/folded constants and reference globals round-trip; invalid globals preserve output")
