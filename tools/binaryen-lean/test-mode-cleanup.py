#!/usr/bin/env python3
"""Independent wire/Node checks of the mode-selecting byte optimizer."""

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
    data = text.encode("utf-8")
    return bytes([len(data)]) + data


def wrapper(delta, extra_export=False):
    # Standard wire bytes independently authored, without our assembler/encoder.
    # One no-argument grow function, initially empty unbounded memory, no start.
    body = bytes([0, 0x41, delta, 0x40, 0, 0x0B])
    return (b"\x00asm\x01\x00\x00\x00"
            + section(1, bytes([1, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([1, 0])) + section(5, bytes([1, 0, 0]))
            + section(7, bytes([3 if extra_export else 2]) + name("grow") + bytes([0, 0])
                      + name("memory") + bytes([2, 0])
                      + (name("again") + bytes([0, 0]) if extra_export else b""))
            + section(10, bytes([1, len(body)]) + body))


with tempfile.TemporaryDirectory(prefix="wasm-mode-cleanup-") as tmp:
    root = Path(tmp)
    original, result = root / "input.wasm", root / "output.wasm"

    def call(*args):
        return subprocess.run([*driver, *map(str, args)], capture_output=True,
                              text=True, timeout=90)

    def execute(path, delta, selected):
        checked = subprocess.run([node, "-e", """
const fs = require('fs');
const bytes = fs.readFileSync(process.argv[1]);
if (!WebAssembly.validate(bytes)) process.exit(1);
const e = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports;
const delta = Number(process.argv[2]);
const selected = process.argv[3] === 'True';
if (e.memory.buffer.byteLength !== 0) process.exit(2);
for (let i = 0; i < 2; i++) {
  if (e.grow() !== (selected ? -1 : i * delta)) process.exit(3);
  if (e.memory.buffer.byteLength !== (selected ? 0 : (i + 1) * delta * 65536)) process.exit(4);
}
""", str(path), str(delta), str(selected)], capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, (checked.returncode, checked.stderr)

    help_result = call("--help")
    assert help_result.returncode == 0, (help_result.returncode, help_result.stderr)
    assert "--trap-grow-failure" in help_result.stdout
    for delta in [0, 1]:
        original.write_bytes(wrapper(delta))
        execute(original, delta, False)
        for rounds in [0, 2]:
            outputs = []
            for mode in ["equivalence", "refinement", "trap-insertion"]:
                converted = call(original, "-o", result, "--mode", mode, "--rounds", rounds)
                assert converted.returncode == 0, (mode, converted.stderr)
                execute(result, delta, False)
                outputs.append(result.read_bytes())
            assert outputs[0] == outputs[1] == outputs[2], "policy silently changed exact cleanup"
            selected_outputs = []
            for mode in ["refinement", "trap-insertion"]:
                converted = call(original, "-o", result, "--select-grow-failure",
                                 "--rounds", rounds, "--mode", mode)
                assert converted.returncode == 0, (mode, converted.stderr)
                execute(result, delta, True)
                selected_outputs.append(result.read_bytes())
            assert selected_outputs[0] == selected_outputs[1]
            assert selected_outputs[0] != outputs[0], "refinement did not change the wrapper"

    # A valid, useful larger module is outside this exact recognizer. It must
    # retain identity fallback, rather than silently drop the extra export.
    original.write_bytes(wrapper(1, extra_export=True))
    assert call(original, "-o", result).returncode == 0
    ordinary = result.read_bytes()
    assert call(original, "-o", result, "--mode", "refinement",
                "--select-grow-failure").returncode == 0
    assert result.read_bytes() == ordinary
    execute(result, 1, False)

    sentinel = b"preserve existing output"
    errors = [[], ["--mode", "invalid"], ["--mode"], ["--rounds", "-1"],
              ["--rounds", "NaN"], ["--rounds"], ["--unknown"],
              ["--select-grow-failure"],
              ["--mode", "equivalence", "--select-grow-failure"]]
    for flags in errors:
        if not flags:
            args = []
        else:
            args = [root / "missing.wasm", "-o", result, *flags]
        result.write_bytes(sentinel)
        rejected = call(*args)
        assert rejected.returncode == 2, (flags, rejected.returncode, rejected.stderr)
        assert result.read_bytes() == sentinel
        result.unlink()
        assert call(*args).returncode == 2
        assert not result.exists()

    for bad in [b"bad", b"\x00asm\x01\x00\x00\x00\x07\x05\x01\x01x\x00\x00"]:
        original.write_bytes(bad)
        result.write_bytes(sentinel)
        assert call(original, "-o", result, "--mode", "refinement",
                    "--select-grow-failure").returncode == 1
        assert result.read_bytes() == sentinel
    assert call(root / "missing.wasm", "-o", result).returncode == 1
    assert result.read_bytes() == sentinel

print("All policies preserve exact cleanup unless a weaker rewrite is requested")
print("Zero/nonzero growth refinement changed real bytes and preserved two-call state semantics")
print("Incompatible certificates reject before IO; usage/invalid-input/output checks passed")
