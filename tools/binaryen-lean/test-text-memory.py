#!/usr/bin/env python3
"""Real-file integer memory round trips using standalone or shared tools."""

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
# Independently constructed module: run(x) stores and reloads x at byte 4.
body = bytes([0, 0x41, 0, 0x20, 0, 0x36, 2, 4, 0x41, 0, 0x28, 2, 4, 0x0B])
reference = (header + section(1, bytes([1, 0x60, 1, 0x7F, 1, 0x7F]))
             + section(3, bytes([1, 0])) + section(5, bytes([1, 1, 1, 2]))
             + section(7, bytes([2]) + name("run") + bytes([0, 0])
                       + name("memory") + bytes([2, 0]))
             + section(10, bytes([1]) + leb(len(body)) + body))

with tempfile.TemporaryDirectory(prefix="wasm-text-memory-") as tmp:
    root = Path(tmp)
    wat, binary, printed, rebuilt = (root / item for item in
                                    ["input.wat", "input.wasm", "printed.wat", "rebuilt.wasm"])
    wat.write_text((Path(__file__).resolve().parent / "text-tools" / "memory.wat").read_text())

    def call(command, source, target):
        return subprocess.run([*commands[command], str(source), "-o", str(target)],
                              text=True, capture_output=True, check=False)

    def execute(path, full):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
for (const x of [42, -1, 2147483647]) {
  if (e.run(x) !== x || new DataView(e.memory.buffer).getInt32(4, true) !== x) process.exit(1);
}
if (process.argv[2] === 'full') {
  if (e.pages() !== 1 || e.narrow(255) !== -1 || e.narrow(128) !== -128) process.exit(1);
  if (e.wide(8589934591n) !== 8589934591n || e.wide(-1n) !== -1n) process.exit(1);
  if (e.peek(4) !== 2147483647) process.exit(1);
  let trapped = false;
  try { e.peek(e.memory.buffer.byteLength - 2); } catch (error) {
    if (!(error instanceof WebAssembly.RuntimeError)) throw error;
    trapped = true;
  }
  if (!trapped || e.grow(1) !== 1 || e.pages() !== 2 || e.grow(1) !== -1 || e.pages() !== 2)
    process.exit(1);
}
""", str(path), "full" if full else "small"], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute(binary, True)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert "(memory 1 2)" in printed.read_text()
    assert 'i32.store 0 offset=4 align=4' in printed.read_text()
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute(rebuilt, True)

    binary.write_bytes(reference)
    execute(binary, False)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute(rebuilt, False)
    print("Memory text/binary round trips passed, including independent wire bytes")
    print("Node checked full/packed integer accesses, byte order, bounds traps and growth" if node else
          "Node unavailable; independent execution checks skipped")

    # Multiple memories are supported by the expanded canonical serializer.
    multiple_memories = header + section(5, bytes([2, 0, 1, 0, 1]))
    binary.write_bytes(multiple_memories)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert printed.read_text() == "(module (memory 1) (memory 1))"
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    assert rebuilt.read_bytes() == multiple_memories

    sentinel = b"preserve existing output"
    for text in ["(module (memory i64 1))", "(module (memory 1) (memory 1))",
                 '(module (import "env" "m" (memory 1)))',
                 '(module (memory 1) (data "x" "y"))']:
        wat.write_text(text)
        result = call("as", wat, binary)
        assert result.returncode == 0, (text, result.stderr)
        result = call("dis", binary, printed)
        assert result.returncode == 0, result.stderr
        result = call("as", printed, rebuilt)
        assert result.returncode == 0, result.stderr
        assert binary.read_bytes() == rebuilt.read_bytes()
    for text in ["(module (memory 65537))", "(module (memory 2 1))"]:
        wat.write_text(text)
        binary.write_bytes(sentinel)
        result = call("as", wat, binary)
        assert result.returncode == 1, (text, result.returncode, result.stderr)
        assert binary.read_bytes() == sentinel
    print("Memory64, multiple/imported memories and concatenated data round-trip; invalid limits preserve output")
