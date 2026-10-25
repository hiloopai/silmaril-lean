#!/usr/bin/env python3
"""Real-file as/dis checks; pass the toolkit command (including lean --run).

python3 tools/binaryen-lean/test-text-tools.py .lake/build/bin/binaryen-tools-lean
"""

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
    as_driver, dis_driver = arguments[1:split], arguments[split + 1:]
    assert as_driver and dis_driver, "Both standalone driver commands are required"
    commands = {"as": as_driver, "dis": dis_driver}
else:
    driver = arguments or [".lake/build/bin/binaryen-tools-lean"]
    commands = {command: [*driver, command] for command in ["as", "dis"]}
node = shutil.which("node")
header = b"\x00asm\x01\x00\x00\x00"
source = (Path(__file__).resolve().parent / "text-tools" / "integer-locals.wat").read_text()

# Independent binary fixture for the same computation: run(x) = 2*x + 2.
body = bytes([1, 1, 0x7F, 0x20, 0, 0x41, 2, 0x6C, 0x21, 1,
              0x20, 1, 0x41, 2, 0x6A, 0x0B])
reference = (header + section(1, bytes([1, 0x60, 1, 0x7F, 1, 0x7F]))
             + section(3, bytes([1, 0]))
             + section(7, bytes([1]) + name("run") + bytes([0, 0]))
             + section(10, bytes([1]) + leb(len(body)) + body))

with tempfile.TemporaryDirectory(prefix="wasm-text-tools-") as tmp:
    root = Path(tmp)
    wat = root / "input.wat"
    binary = root / "assembled.wasm"
    printed = root / "printed.wat"
    rebuilt = root / "rebuilt.wasm"
    wat.write_text(source)

    def call(command, input_path, output_path):
        return subprocess.run([*commands[command], str(input_path), "-o", str(output_path)],
                              text=True, capture_output=True, check=False)

    def execute(path):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const instance = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])));
for (const [x, expected] of [[0,2], [20,42], [-1,0], [2147483647,0]]) {
  if (instance.exports.run(x) !== expected) process.exit(1);
}
""", str(path)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    assembled = call("as", wat, binary)
    assert assembled.returncode == 0, assembled.stderr
    assert binary.read_bytes().startswith(header)
    execute(binary)
    disassembled = call("dis", binary, printed)
    assert disassembled.returncode == 0, disassembled.stderr
    assert printed.read_text().lstrip().startswith("(module")
    again = call("as", printed, rebuilt)
    assert again.returncode == 0, again.stderr
    execute(rebuilt)

    independent = root / "independent.wasm"
    independent.write_bytes(reference)
    execute(independent)
    assert call("dis", independent, printed).returncode == 0
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute(rebuilt)
    print("as/dis round trips preserve an exported parameter/local computation")
    print("Node checked ordinary, negative and wrapping inputs" if node else
          "Node unavailable; independent execution checks skipped")

    control_source = (Path(__file__).resolve().parent / "text-tools" / "control-flow.wat").read_text()

    def execute_control(path):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const i = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])));
for (const [x, expected] of [[0,9], [1,7], [-1,7]]) {
  if (i.exports.choose(x) !== expected) process.exit(1);
}
for (const x of [0,1,32]) {
  if (i.exports.countdown(x) !== 0) process.exit(1);
}
""", str(path)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    wat.write_text(control_source)
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute_control(binary)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    assert binary.read_bytes() == rebuilt.read_bytes()
    execute_control(rebuilt)

    # Independently written wire-format control instructions, not encoder output.
    choose_body = bytes([0, 0x20, 0, 0x04, 0x7F,
                         0x02, 0x7F, 0x41, 7, 0x0B, 0x05,
                         0x03, 0x7F, 0x41, 9, 0x0B, 0x0B, 0x0B])
    countdown_body = bytes([0, 0x02, 0x40, 0x03, 0x40,
                            0x20, 0, 0x45, 0x0D, 1,
                            0x20, 0, 0x41, 1, 0x6B, 0x21, 0, 0x0C, 0,
                            0x0B, 0x0B, 0x20, 0, 0x0B])
    independent.write_bytes(header
                            + section(1, bytes([1, 0x60, 1, 0x7F, 1, 0x7F]))
                            + section(3, bytes([2, 0, 0]))
                            + section(7, bytes([2]) + name("choose") + bytes([0, 0])
                                      + name("countdown") + bytes([0, 1]))
                            + section(10, bytes([2]) + leb(len(choose_body)) + choose_body
                                      + leb(len(countdown_body)) + countdown_body))
    execute_control(independent)
    result = call("dis", independent, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute_control(rebuilt)
    print("Structured as/dis round trips preserve nested branches and a countdown loop")

    import_source = (Path(__file__).resolve().parent / "text-tools" / "host-import.wat").read_text()

    def execute_import(path):
        if not node:
            return
        result = subprocess.run([node, "-e", """
const fs = require('fs');
let calls = 0;
const host = {env: {twice: x => { calls++; return Math.imul(x, 2); }}};
const i = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])), host);
for (const [x, expected] of [[0,2], [20,42], [-1,0], [2147483647,0]]) {
  if (i.exports.run(x) !== expected) process.exit(1);
}
if (i.exports.host(5) !== 10 || calls !== 5) process.exit(1);
""", str(path)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr

    wat.write_text(import_source)
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    execute_import(binary)
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    assert binary.read_bytes() == rebuilt.read_bytes()
    execute_import(rebuilt)

    import_body = bytes([0, 0x20, 0, 0x10, 0, 0x41, 2, 0x6A, 0x0B])
    independent.write_bytes(header
                            + section(1, bytes([1, 0x60, 1, 0x7F, 1, 0x7F]))
                            + section(2, bytes([1]) + name("env") + name("twice") + bytes([0, 0]))
                            + section(3, bytes([1, 0]))
                            + section(7, bytes([2]) + name("host") + bytes([0, 0])
                                      + name("run") + bytes([0, 1]))
                            + section(10, bytes([1]) + leb(len(import_body)) + import_body))
    execute_import(independent)
    result = call("dis", independent, printed)
    assert result.returncode == 0, result.stderr
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    execute_import(rebuilt)
    print("Function-import round trips preserve host calls and imported/defined export indices")

    sentinel = b"preserve existing output"

    # Successful syntactic disassembly does not imply module validity or
    # successful reassembly: function 0 does not exist in this module.
    dangling = root / "dangling-export.wasm"
    dangling.write_bytes(header + section(7, bytes([1]) + name("x") + bytes([0, 0])))
    result = call("dis", dangling, printed)
    assert result.returncode == 0, result.stderr
    assert printed.read_text() == '(module (export "x" (func 0)))'
    rebuilt.write_bytes(sentinel)
    result = call("as", printed, rebuilt)
    assert result.returncode == 1, result.stderr
    assert "module validation failed" in result.stderr
    assert rebuilt.read_bytes() == sentinel

    # Plain Unicode names use the checked UTF-8 fallback when the original
    # escaped-byte printer cannot be relexed. Exercise both an assembled file
    # and independently constructed bytes rather than only an encoder loop.
    wat.write_text('(module (type (func (param) (result))) '
                   '(func (type 0) (local)) (export "é" (func 0)))')
    result = call("as", wat, binary)
    assert result.returncode == 0, result.stderr
    result = call("dis", binary, printed)
    assert result.returncode == 0, result.stderr
    assert '(export "é" (func 0))' in printed.read_text()
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    unicode_body = bytes([0, 0x0B])
    independent.write_bytes(header + section(1, bytes([1, 0x60, 0, 0]))
                            + section(3, bytes([1, 0]))
                            + section(7, bytes([1]) + name("é") + bytes([0, 0]))
                            + section(10, bytes([1]) + leb(len(unicode_body)) + unicode_body))
    result = call("dis", independent, printed)
    assert result.returncode == 0, result.stderr
    assert '(export "é" (func 0))' in printed.read_text()
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    if node:
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const instance = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])));
if (typeof instance.exports['é'] !== 'function') process.exit(1);
instance.exports['é']();
""", str(rebuilt)], text=True, capture_output=True, check=False)
        assert result.returncode == 0, result.stderr
    print("Unicode export names round-trip from original text and independent binary bytes")
    print("Round-trip acceptance remains conditional: invalid exports reject during reassembly")

    for text in ["(module) trailing", "(module", "(module (unknown))",
                 "(module (func (type 99)))",
                 "(module (type (func (param) (result i32))) (func (type 0) (local) (block (result i32) br 0)))"]:
        wat.write_text(text)
        binary.write_bytes(sentinel)
        result = call("as", wat, binary)
        assert result.returncode == 1, (text, result.returncode, result.stderr)
        assert binary.read_bytes() == sentinel

    # Independently encoded memory64 now round-trips through both tools.
    memory64 = header + section(5, bytes([1, 4, 1]))
    independent.write_bytes(memory64)
    result = call("dis", independent, printed)
    assert result.returncode == 0, result.stderr
    assert printed.read_text() == "(module (memory i64 1))"
    result = call("as", printed, rebuilt)
    assert result.returncode == 0, result.stderr
    assert rebuilt.read_bytes() == memory64

    # 0xff is an invalid memory-limits flag, unlike memory64's valid flag 4.
    for data in [b"", header + b"\xff", header + section(5, bytes([1, 0xff, 1]))]:
        independent.write_bytes(data)
        printed.write_bytes(sentinel)
        result = call("dis", independent, printed)
        assert result.returncode == 1, (data, result.returncode, result.stderr)
        assert printed.read_bytes() == sentinel

    absent = root / "absent.wat"
    assert call("dis", independent, absent).returncode == 1
    assert not absent.exists()
    assert call("as", root / "missing.wat", binary).returncode == 1
    for command in ["as", "dis"]:
        result = subprocess.run(commands[command], capture_output=True, check=False)
        assert result.returncode == 2
    print("Malformed/unsupported inputs reject before writing; IO/usage errors distinguished")
