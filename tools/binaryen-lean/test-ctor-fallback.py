#!/usr/bin/env python3
"""Actual validated bytes: transform the narrow family; preserve other modules."""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

driver = sys.argv[1:]
if not driver:
    raise SystemExit("pass the compatibility executable or Lean API adapter command")
node = shutil.which("node")
if node is None:
    raise SystemExit("Node is required")


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def name(text):
    data = text.encode()
    return bytes([len(data)]) + data


def ctor_fixture(trap=False):
    ctor = bytes([0, 0, 0x0B]) if trap else bytes([0, 0x41, 9, 0x24, 0, 0x0B])
    getter = bytes([0, 0x23, 0, 0x0B])
    return (b"\0asm\x01\0\0\0"
            + section(1, bytes([2, 0x60, 0, 0, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([2, 0, 1]))
            + section(6, bytes([1, 0x7F, 1, 0x41, 3, 0x0B]))
            + section(7, bytes([2]) + name("get") + bytes([0, 1])
                      + name("state") + bytes([3, 0]))
            + section(8, bytes([0]))
            + section(10, bytes([2, len(ctor)]) + ctor + bytes([len(getter)]) + getter))


with tempfile.TemporaryDirectory(prefix="ctor-fallback-") as tmp:
    root = Path(tmp)
    source, target = root / "in.wasm", root / "out.wasm"

    def call(data):
        source.write_bytes(data)
        return subprocess.run([*driver, str(source), "-o", str(target)],
                              capture_output=True, text=True, timeout=90)

    transformed = call(ctor_fixture())
    assert transformed.returncode == 0 and "transformed" in transformed.stderr, transformed.stderr
    assert target.read_bytes() != source.read_bytes()
    checked = subprocess.run([node, "-e", """
const fs = require('fs');
const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1]))).exports;
if (e.get() !== 9 || e.state.value !== 9) process.exit(1);
""", str(target)], capture_output=True, text=True, timeout=30)
    assert checked.returncode == 0, checked.stderr

    # Standalone globals have no matching constructor; keep original bytes and metadata.
    standalone = (b"\0asm\x01\0\0\0"
                  + section(0, name("keep") + b"metadata")
                  + section(6, bytes([1, 0x7F, 1, 0x41, 7, 0x0B]))
                  + section(7, bytes([1]) + name("state") + bytes([3, 0])))
    for data in [standalone, ctor_fixture(trap=True), b"\0asm\x01\0\0\0"]:
        kept = call(data)
        assert kept.returncode == 0 and "skipped" in kept.stderr, kept.stderr
        assert target.read_bytes() == data, "fallback did not retain original bytes"

    sentinel = b"retain output on error"
    for data in [b"bad", b"\0asm\x01\0\0\0" + section(8, bytes([0]))]:
        target.write_bytes(sentinel)
        rejected = call(data)
        assert rejected.returncode == 1, rejected.stderr
        assert target.read_bytes() == sentinel

print("ctor total-fallback bytes/Node checks passed")
