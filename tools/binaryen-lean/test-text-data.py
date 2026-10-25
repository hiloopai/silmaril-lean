#!/usr/bin/env python3
"""Active/passive data real-file round trips and independent wire/Node checks."""

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
bodies = [bytes([0, 0x20, 0, 0x20, 1, 0x20, 2, 0xFC, 8, 1, 0, 0x0B]),
          bytes([0, 0x20, 0, 0x2D, 0, 0, 0x0B]), bytes([0, 0xFC, 9, 1, 0x0B])]
exports = [("init", 0, 0), ("byte", 0, 1), ("drop", 0, 2), ("memory", 2, 0)]
# Hand-built wire bytes use the standard section order: data-count before code.
# memory.init encodes data index before memory index, unlike the text spelling.
reference = (header
             + section(1, bytes([3, 0x60, 3, 0x7F, 0x7F, 0x7F, 0,
                                0x60, 1, 0x7F, 1, 0x7F, 0x60, 0, 0]))
             + section(3, bytes([3, 0, 1, 2])) + section(5, bytes([1, 0, 1]))
             + section(7, leb(len(exports)) + b"".join(
                 name(text) + bytes([kind]) + leb(index) for text, kind, index in exports))
             + section(12, bytes([2]))
             + section(10, leb(len(bodies)) + b"".join(leb(len(body)) + body for body in bodies))
             + section(11, bytes([2, 0, 0x41, 4, 0x0B, 4]) + b"Lean"
                       + bytes([1, 4]) + b"WASM"))

with tempfile.TemporaryDirectory(prefix="wasm-text-data-") as tmp:
    root = Path(tmp)
    wat, binary, printed, rebuilt = (root / item for item in
                                    ["input.wat", "input.wasm", "printed.wat", "rebuilt.wasm"])
    wat.write_text((Path(__file__).resolve().parent / "text-tools" / "data.wat").read_text())

    def call(command, source, target):
        return subprocess.run([*commands[command], str(source), "-o", str(target)],
                              text=True, capture_output=True, check=False)

    def execute(path):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
const bytes = new Uint8Array(e.memory.buffer);
const same = (offset, expected) => expected.every((value, i) => bytes[offset + i] === value);
const trap = action => {
  try { action(); } catch (error) {
    if (error instanceof WebAssembly.RuntimeError) return;
    throw error;
  }
  throw new Error('expected a Wasm bounds trap');
};
if (!same(4, [76, 101, 97, 110]) || e.byte(4) !== 76 || bytes[0] !== 0)
  process.exit(1);
e.init(16, 0, 4);
e.init(32, 1, 2);
if (!same(16, [87, 65, 83, 77]) || !same(32, [65, 83])) process.exit(1);
trap(() => e.init(65535, 0, 2));
trap(() => e.init(0, 3, 2));
trap(() => e.init(0, -1, 1));
if (bytes[0] !== 0 || bytes[65535] !== 0) process.exit(1);
e.drop();
e.drop();
e.init(0, 0, 0);
e.init(65536, 0, 0);
trap(() => e.init(65537, 0, 0));
trap(() => e.init(0, 0, 1));
if (!same(4, [76, 101, 97, 110]) || !same(16, [87, 65, 83, 77])) process.exit(1);
""", str(path)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute(binary)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert '(data (memory 0) (offset i32.const 4) "Lean")' in printed.read_text()
    assert '(data "WASM")' in printed.read_text()
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
    print("Active/passive data round trips passed, including independent wire bytes")
    print("Node checked active initialization, passive copies, drops and bounds traps" if node else
          "Node unavailable; independent execution checks skipped")

    # UTF-8 data is bytes; inspect the exact encoding after both conversions.
    # Include imported functions and globals to exercise all existing spaces.
    wat.write_text('(module (type (func (param) (result i32))) '
                   '(import "env" "f" (func (type 0))) (memory 1) '
                   '(global i32 i32.const 42) '
                   '(func (type 0) (local) call 0 global.get 0 i32.add) '
                   '(data (memory 0) (offset i32.const 8) "é") (data "x") '
                   '(export "run" (func 1)) (export "memory" (memory 0)))')
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert '"é"' in printed.read_text()
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    if node:
        result = subprocess.run([node, "-e", """
const fs = require('fs');
for (const path of process.argv.slice(1)) {
  const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path)),
    {env: {f: () => 42}}).exports;
  const bytes = new Uint8Array(e.memory.buffer);
  if (e.run() !== 84 || bytes[8] !== 0xC3 || bytes[9] !== 0xA9 || bytes[10] !== 0)
    process.exit(1);
}
""", str(binary), str(rebuilt)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr
    print("Exact UTF-8 data bytes compose with function imports and integer globals")

    # Neither input passes through our binary encoder to construct the oracle.
    # Active memory makes every byte observable in an independent engine.
    payload = bytes([0, 255, 34, 92, 10, 127])
    byte_reference = (header + section(5, bytes([1, 0, 1]))
                      + section(7, bytes([1]) + name("memory") + bytes([2, 0]))
                      + section(11, bytes([1, 0, 0x41, 16, 0x0B])
                                + leb(len(payload)) + payload))

    def execute_bytes(path, expected=payload):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
const bytes = new Uint8Array(e.memory.buffer);
const expected = Array.from(Buffer.from(process.argv[2], 'hex'));
if (bytes[15] !== 0 || bytes[16 + expected.length] !== 0 ||
    !expected.every((value, i) => bytes[16 + i] === value)) process.exit(1);
""", str(path), expected.hex()], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    wat.write_text((Path(__file__).resolve().parent / "text-tools" / "byte-data.wat").read_text())
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute_bytes(binary)
    for wire in [binary.read_bytes(), byte_reference]:
        binary.write_bytes(wire)
        execute_bytes(binary)
        result = call("dis", binary, printed)
        assert result.returncode == 0, result.stderr
        assert '"\\00\\ff\\22\\5c\\0a\\7f"' in printed.read_text()
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, result.stderr
        execute_bytes(rebuilt)
    print("Hexadecimal 00/ff/quote/backslash/control bytes passed text and independent wire round trips")
    print("Node checked every active byte after assembly and disassembly/reassembly" if node else
          "Node unavailable; byte execution checks skipped")

    # Exhaust the byte alphabet, using uppercase text hex and an independently
    # constructed active binary. Node observes every value after each route.
    all_bytes = bytes(range(256))
    uppercase = "".join(f"\\{value:02X}" for value in all_bytes)
    wat.write_text('(module (memory 1) (data (memory 0) (offset i32.const 16) "'
                   + uppercase + '") (export "memory" (memory 0)))')
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute_bytes(binary, all_bytes)
    binary.write_bytes(header + section(5, bytes([1, 0, 1]))
                       + section(7, bytes([1]) + name("memory") + bytes([2, 0]))
                       + section(11, bytes([1, 0, 0x41, 16, 0x0B])
                                 + leb(len(all_bytes)) + all_bytes))
    execute_bytes(binary, all_bytes)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute_bytes(rebuilt, all_bytes)
    print("All 256 byte values passed uppercase-hex assembly and independent-wire dis/as checks")

    # Extended-constant offsets now retain their complete instruction sequence.
    extended_offset = (header + section(5, bytes([1, 0, 1])) + section(12, bytes([1]))
                       + section(11, bytes([1, 0, 0x41, 0, 0x41, 1, 0x6A,
                                            0x0B, 1, ord("x")])))
    binary.write_bytes(extended_offset)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert '(offset i32.const 0 i32.const 1 i32.add)' in printed.read_text()
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    assert rebuilt.read_bytes() == extended_offset

    sentinel = b"preserve existing output"
    for text in ['(module (memory 1) (data (memory 0) '
                 '(offset i32.const 0 i32.const 1 i32.add) "x"))',
                 '(module (memory 1) (data (i32.const 0) "x"))',
                 '(module (data "x" "y"))', '(module (data $d "x"))',
                 '(module (data "x") (memory 1))']:
        wat.write_text(text)
        result = call("as", wat, binary)
        assert result.returncode == 0, (text, result.stderr)
        result = call("dis", binary, printed)
        assert result.returncode == 0, result.stderr
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, result.stderr
        assert binary.read_bytes() == rebuilt.read_bytes()
    for text in ['(module (memory 1) (data (memory 1) (offset i32.const 0) "x"))',
                 '(module (data (memory 0) (offset i32.const 0) "x"))',
                 '(module (memory 1) (data (memory 0) (offset i64.const 0) "x"))',
                 '(module (type (func (param) (result))) (memory 1) '
                 '(func (type 0) (local) i32.const 0 i32.const 0 i32.const 1 '
                 'memory.init 0 1) (data "x"))',
                 '(module (type (func (param) (result))) (memory 1) '
                 '(func (type 0) (local) memory.init 0 0) (data "x"))',
                 '(module (type (func (param) (result))) '
                 '(func (type 0) (local) data.drop 1) (data "x"))']:
        wat.write_text(text)
        binary.write_bytes(sentinel)
        result = call("as", wat, binary)
        assert result.returncode == 1, (text, result.returncode, result.stderr)
        assert binary.read_bytes() == sentinel
    # The expanded certified frontend supports mnemonic and Unicode escapes.
    # Check their exact bytes independently, rather than only accepting a round
    # trip through our own parser and printer.
    for escape, payload in [(r"\t", b"\t"), (r"\n", b"\n"), (r"\r", b"\r"),
                            (r'\"', b'"'), (r"\'", b"'"), (r"\\", b"\\"),
                            (r"\u{41}", b"A"), (r"\u{e9}", "é".encode()),
                            (r"\u{1_F642}", "🙂".encode())]:
        wat.write_text('(module (memory 1) (data (i32.const 16) "' + escape
                       + '") (export "memory" (memory 0)))')
        result = call("as", wat, binary)
        assert result.returncode == 0, (escape, result.stderr)
        assert binary.read_bytes().endswith(section(
            11, bytes([1, 0, 0x41, 16, 0x0B]) + leb(len(payload)) + payload))
        execute_bytes(binary, payload)
        result = call("dis", binary, printed)
        assert result.returncode == 0, (escape, result.stderr)
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, (escape, result.stderr)
        assert rebuilt.read_bytes() == binary.read_bytes()
        execute_bytes(rebuilt, payload)
    print("Mnemonic and Unicode escapes retain exact independently checked bytes")
    # Malformed escapes still reject before overwriting output.
    for escape in [r"\0", r"\gg", r"\0g", r"\g0", r"\q", r"\u{}",
                   r"\u{110000}", r"\u{xyz}", r"\u{41"]:
        text = '(module (data "' + escape + '"))'
        wat.write_text(text)
        binary.write_bytes(sentinel)
        result = call("as", wat, binary)
        assert result.returncode == 1, (text, result.returncode, result.stderr)
        assert binary.read_bytes() == sentinel
    # Independent passive wire fixtures also accept non-UTF8 data, without
    # weakening the separate requirement that import/export names be UTF-8.
    for payload in [b'\x00', b'"', b'\\', b'\n', b'\x7f', b'\xff']:
        wire = header + section(11, bytes([1, 1]) + leb(len(payload)) + payload)
        if node:
            result = subprocess.run([node, "-e", """
if (!WebAssembly.validate(Buffer.from(process.argv[1], 'hex'))) process.exit(1);
""", wire.hex()], text=True, capture_output=True, check=False)
            assert result.returncode == 0, result.stderr
        binary.write_bytes(wire)
        result = call("dis", binary, printed)
        assert result.returncode == 0, (payload, result.returncode, result.stderr)
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, (payload, result.returncode, result.stderr)
        assert rebuilt.read_bytes().endswith(section(11, bytes([1, 1]) + leb(len(payload)) + payload))
    print("Arbitrary passive bytes round-trip; malformed syntax/escapes preserve output")
