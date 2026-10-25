#!/usr/bin/env python3
"""Total metadce: real optimized bytes vs exact valid unsupported input bytes."""
import json
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


def fixture(memory):
    bodies = [bytes([0, 0x41, 42, 0x0B]), bytes([0, 0x41, 17, 0x0B])]
    return (b"\0asm\x01\0\0\0"
            + section(0, name("keep") + b"metadata")
            + section(1, bytes([1, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([2, 0, 0]))
            + (section(5, bytes([1, 0, 1])) if memory else b"")
            + section(7, bytes([2]) + name("entry") + bytes([0, 0])
                      + name("unused") + bytes([0, 1]))
            + section(10, bytes([2]) + b"".join(bytes([len(b)]) + b for b in bodies)))


with tempfile.TemporaryDirectory(prefix="metadce-fallback-") as tmp:
    root = Path(tmp)
    source, graphfile, target = root / "in.wasm", root / "graph.json", root / "out.wasm"

    def call(data, graph):
        source.write_bytes(data)
        graphfile.write_text(json.dumps(graph))
        return subprocess.run([*driver, str(source), "--graph-file", str(graphfile), "-o", str(target)],
                              capture_output=True, text=True, timeout=90)

    graph = [{"name": "entryNode", "export": "entry", "root": True}]
    converted = call(fixture(False), graph)
    assert converted.returncode == 0 and "applied" in converted.stderr, converted.stderr
    assert target.read_bytes() != source.read_bytes()
    kept = call(fixture(True), graph)
    assert kept.returncode == 0 and "skipped" in kept.stderr, kept.stderr
    assert target.read_bytes() == source.read_bytes(), "unsupported valid module was not kept exactly"
    checked = subprocess.run([node, "-e", """
const fs = require('fs');
for (const path of process.argv.slice(1)) {
  const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path))).exports;
  if (e.entry() !== 42 || e.unused() !== 17) process.exit(1);
}
""", str(source), str(target)], capture_output=True, text=True, timeout=30)
    assert checked.returncode == 0, checked.stderr
    sentinel = b"retain on rejection"
    # Graph errors still reject outside the optimization fragment.
    for badgraph in [[{"name": "a", "export": "absent"}],
                     [{"name": "a", "reaches": ["missing"]}],
                     [{"name": "a", "root": False}],
                     [{"name": "a", "import": ["env", "f"]}]]:
        target.write_bytes(sentinel)
        rejected = call(fixture(True), badgraph)
        assert rejected.returncode == 1, rejected.stderr
        assert target.read_bytes() == sentinel
    for invalid in [b"bad", b"\0asm\x01\0\0\0" + section(8, bytes([0]))]:
        target.write_bytes(sentinel)
        assert call(invalid, []).returncode == 1
        assert target.read_bytes() == sentinel

print("metadce total-fallback bytes/Node checks passed")
