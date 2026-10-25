#!/usr/bin/env python3
"""Independent real-file checks of the bounded shell and its retained legacy entry.

Pass the standalone driver command, optionally followed by --legacy-driver and
the toolkit driver command. No fixture uses our assembler, decoder or encoder.
"""

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

commands = sys.argv[1:]
if "--legacy-driver" in commands:
    split = commands.index("--legacy-driver")
    driver, legacy = commands[:split], commands[split + 1:]
    assert driver and legacy, "both driver commands are required"
else:
    driver = commands or [".lake/build/bin/wasm-shell-lean"]
    legacy = []
node = shutil.which("node")
if node is None:
    raise SystemExit("Node is required for the independent reference checks")


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def name(text):
    data = text.encode("utf-8")
    return bytes([len(data)]) + data


def module(types, signatures, bodies, *, global_payload=None, start=None, imports=None):
    wire = b"\x00asm\x01\x00\x00\x00" + section(1, bytes([len(types)]) + b"".join(types))
    if imports is not None:
        wire += section(2, imports)
    if signatures:
        wire += section(3, bytes([len(signatures), *signatures]))
    if global_payload is not None:
        wire += section(6, global_payload)
    wire += section(7, bytes([1]) + name("run") + bytes([0, 0]))
    if start is not None:
        wire += section(8, bytes([start]))
    if bodies:
        wire += section(10, bytes([len(bodies)]) + b"".join(bytes([len(b)]) + b for b in bodies))
    return wire


i32_result = bytes([0x60, 0, 1, 0x7F])
i32_identity = bytes([0x60, 1, 0x7F, 1, 0x7F])
unit = bytes([0x60, 0, 0])
answer = module([i32_result], [0], [bytes([0, 0x41, 42, 0x0B])])
identity = module([i32_identity], [0], [bytes([0, 0x20, 0, 0x0B])])
trapped = module([i32_result], [0], [bytes([0, 0, 0x0B])])
looping = module([i32_result], [0], [bytes([0, 0x03, 0x40, 0x0C, 0, 0x0B, 0, 0x0B])])
get_global = bytes([0, 0x23, 0, 0x0B])
set_global = bytes([0, 0x41, 42, 0x24, 0, 0x0B])
global_payload = bytes([1, 0x7F, 1, 0x41, 0, 0x0B])
started = module([i32_result, unit], [0, 1], [get_global, set_global],
                 global_payload=global_payload, start=1)
start_trap = module([i32_result, unit], [0, 1], [get_global, bytes([0, 0, 0x0B])],
                    global_payload=global_payload, start=1)
start_loop = module([i32_result, unit], [0, 1],
                    [get_global, bytes([0, 0x03, 0x40, 0x0C, 0, 0x0B, 0x0B])],
                    global_payload=global_payload, start=1)
imported = module([i32_result], [], [],
                  imports=bytes([1]) + name("host") + name("f") + bytes([0, 0]))
invalid = module([i32_result], [0], [bytes([0, 0x0B])])


with tempfile.TemporaryDirectory(prefix="wasm-shell-") as tmp:
    root = Path(tmp)
    files = {}
    for label, wire in [("answer", answer), ("identity", identity), ("trap", trapped),
                        ("loop", looping), ("start", started), ("start-trap", start_trap),
                        ("start-loop", start_loop), ("imports", imported), ("invalid", invalid),
                        ("malformed", b"not a wasm module")]:
        path = root / f"{label}.wasm"
        path.write_bytes(wire)
        files[label] = path

    def call(command, *args):
        return subprocess.run([*command, *map(str, args)], capture_output=True,
                              text=True, timeout=90)

    def check(path, *, fuel=100, export="run", args=(), status=0, output="", error=""):
        request = [str(fuel), str(path), export, *map(str, args)]
        result = call(driver, *request)
        assert result.returncode == status, (request, result.returncode, result.stdout, result.stderr)
        assert result.stdout == output, (request, result.stdout)
        assert error in result.stderr, (request, result.stderr)
        if not error:
            assert not result.stderr, (request, result.stderr)
        if legacy:
            previous = call(legacy, "shell", *request)
            assert (previous.returncode, previous.stdout, previous.stderr) == (
                result.returncode, result.stdout, result.stderr), request

    def reference(path, *args, expected=42, trap=False):
        result = call([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
const args = process.argv.slice(4).map(Number);
if (process.argv[3] === 'True') {
  try { e.run(...args); process.exit(1); }
  catch (error) { if (!(error instanceof WebAssembly.RuntimeError)) throw error; }
} else if (e.run(...args) !== Number(process.argv[2])) process.exit(2);
"""], path, expected, trap, *args)
        assert result.returncode == 0, (path, result.stderr)

    help_result = call(driver, "--help")
    assert help_result.returncode == 0 and "usage:" in help_result.stdout
    assert "FUEL MODULE.wasm EXPORT" in help_result.stdout
    assert "inconclusive" in help_result.stdout and "deterministic" in help_result.stdout
    reference(files["answer"])
    reference(files["start"])
    reference(files["identity"], -1, expected=-1)
    reference(files["trap"], trap=True)
    check(files["answer"], output="return [i32:42]\n")
    check(files["identity"], args=[-1], output="return [i32:4294967295]\n")
    check(files["identity"], args=[4294967297], output="return [i32:1]\n")
    check(files["trap"], status=4, output="trap\n")
    check(files["start"], output="return [i32:42]\n")
    check(files["start-trap"], status=4, error="initialization ended with")
    check(files["answer"], fuel=0, status=3, error="initialization; result is inconclusive")
    check(files["answer"], fuel=1, status=3, error="invocation; result is inconclusive")
    check(files["loop"], fuel=30, status=3, error="invocation; result is inconclusive")
    check(files["start-loop"], fuel=30, status=3, error="initialization; result is inconclusive")
    check(files["answer"], export="missing", status=1, error="export is absent")
    check(files["answer"], args=[7], status=1, error="argument types")
    check(files["imports"], status=1, error="imports, or concrete initialization failed")
    check(files["invalid"], status=1, error="validation, imports, or concrete initialization failed")
    check(files["malformed"], status=1, error="shell: module:")
    for request in [[], ["100"], ["100", "missing.wasm"],
                    ["-1", "missing.wasm", "run"], ["NaN", "missing.wasm", "run"],
                    ["100", "missing.wasm", "run", "bad-integer"]]:
        result = call(driver, *request)
        assert result.returncode == 2, (request, result.returncode, result.stderr)
        assert not result.stdout
    missing = call(driver, "100", root / "absent.wasm", "run")
    assert missing.returncode == 1 and not missing.stdout

print("Independent bytes and Node: return, wrapped i32 arguments, trap and state-changing start passed")
print("Initialization/invocation fuel are inconclusive; invalid requests/bytes and imports reject")
if legacy:
    print("Legacy binaryen-tools-lean shell preserved statuses, stdout and stderr for every file case")
