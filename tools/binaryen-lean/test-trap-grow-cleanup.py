#!/usr/bin/env python3
"""Independent literal-growth fatal-OOM bytes/Node and mode-gating checks."""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

driver = sys.argv[1:] or [".lake/build/bin/wasm-opt-modes-lean"]
node = shutil.which("node")
if node is None:
    raise SystemExit("Node is required for the independent execution checks")


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def name(text):
    data = text.encode()
    return bytes([len(data)]) + data


def wrapper(delta=0, extra_export=False):
    body = bytes([0, 0x41, delta, 0x40, 0, 0x0B])
    return (b"\x00asm\x01\x00\x00\x00"
            + section(1, bytes([1, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([1, 0])) + section(5, bytes([1, 0, 0]))
            + section(7, bytes([3 if extra_export else 2]) + name("grow") + bytes([0, 0])
                      + name("memory") + bytes([2, 0])
                      + (name("again") + bytes([0, 0]) if extra_export else b""))
            + section(10, bytes([1, len(body)]) + body))


with tempfile.TemporaryDirectory(prefix="wasm-trap-grow-") as tmp:
    root = Path(tmp)
    original, output = root / "source.wasm", root / "guarded.wasm"

    def call(*args):
        return subprocess.run([*driver, *map(str, args)], capture_output=True,
                              text=True, timeout=90)

    def execute(path, delta=0):
        result = subprocess.run([node, "-e", """
const fs = require('fs');
const bytes = fs.readFileSync(process.argv[1]);
if (!WebAssembly.validate(bytes)) process.exit(1);
const e = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports;
const delta = Number(process.argv[2]);
for (let i = 0; i < 3; i++) {
  if (e.grow() !== i * delta) process.exit(2);
  if (e.memory.buffer.byteLength !== (i + 1) * delta * 65536) process.exit(3);
}
""", str(path), str(delta)], capture_output=True, text=True, timeout=30)
        assert result.returncode == 0, (result.returncode, result.stderr)

    help_result = call("--help")
    assert help_result.returncode == 0 and "--trap-grow-failure" in help_result.stdout
    for rounds in [0, 2]:
        for extra in [[], ["--coalesce-locals"]]:
            original.write_bytes(wrapper())
            assert call(original, "-o", output, "--rounds", rounds, *extra).returncode == 0
            unguarded = output.read_bytes()
            guarded = call(original, "-o", output, "--mode", "trap-insertion",
                           "--trap-grow-failure", "--rounds", rounds, *extra)
            assert guarded.returncode == 0, guarded.stderr
            assert output.read_bytes() != unguarded, "real insertion did not change bytes"
            # The output must retain a real memory.grow opcode and a trap opcode.
            assert b"\x40\x00" in output.read_bytes()
            assert b"\x45\x04\x7f\x41\x00\x05\x00\x0b" in output.read_bytes()
            execute(output)

            for delta in [1, 2]:
                original.write_bytes(wrapper(delta))
                assert call(original, "-o", output, "--rounds", rounds, *extra).returncode == 0
                unguarded = output.read_bytes()
                assert call(original, "-o", output, "--mode", "trap-insertion",
                            "--trap-grow-failure", "--rounds", rounds, *extra).returncode == 0
                assert output.read_bytes() != unguarded, "nonzero literal was not guarded"
                assert b"\x40\x00" in output.read_bytes()
                assert b"\x22\x00\x41\x7f\x46\x04\x7f\x00\x05\x20\x00\x0b" in output.read_bytes()
                execute(output, delta)

            original.write_bytes(wrapper(0, True))
            assert call(original, "-o", output, "--rounds", rounds, *extra).returncode == 0
            fallback = output.read_bytes()
            assert call(original, "-o", output, "--mode", "trap-insertion",
                        "--trap-grow-failure", "--rounds", rounds, *extra).returncode == 0
            assert output.read_bytes() == fallback, "unsupported shape lost identity fallback"
            execute(output)

    # -1 is encoded as the one-byte signed LEB127; growth cannot fit the memory32
    # physical bound. Both caught traps leave memory unchanged and callable.
    original.write_bytes(wrapper(127))
    assert call(original, "-o", output, "--mode", "trap-insertion", "--trap-grow-failure").returncode == 0
    physical = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
for (let i = 0; i < 2; i++) {
  let trapped = false;
  try { e.grow(); } catch (error) { trapped = error instanceof WebAssembly.RuntimeError; }
  if (!trapped || e.memory.buffer.byteLength !== 0) process.exit(1);
}
""", str(output)], capture_output=True, text=True, timeout=30)
    assert physical.returncode == 0, physical.stderr

    sentinel = b"preserve existing output"
    for mode in ["equivalence", "refinement"]:
        for exists in [False, True]:
            if exists:
                output.write_bytes(sentinel)
            elif output.exists():
                output.unlink()
            rejected = call(root / "missing.wasm", "-o", output,
                            "--mode", mode, "--trap-grow-failure")
            assert rejected.returncode == 2, rejected.stderr
            assert (output.read_bytes() == sentinel) if exists else not output.exists()
    output.write_bytes(sentinel)
    rejected = call(root / "missing.wasm", "-o", output, "--mode", "trap-insertion",
                    "--trap-grow-failure", "--select-grow-failure")
    assert rejected.returncode == 2 and output.read_bytes() == sentinel
    original.write_bytes(b"bad")
    rejected = call(original, "-o", output, "--mode", "trap-insertion", "--trap-grow-failure")
    assert rejected.returncode == 1 and output.read_bytes() == sentinel

print("Fatal-OOM guard changed real bytes, retained growth, and returned successive old sizes over three Node calls")
print("Both cleanup pipelines/round counts retained fallback; incompatible policies rejected before IO")
print("Physical failure/recovery checked in Node; forced-failure recovery and both widths checked in GrowOOMLiteralTest and all-profile sessions")
