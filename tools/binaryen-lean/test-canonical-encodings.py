#!/usr/bin/env python3
"""Selected wasm-opt accepts valid alternate Core encodings and preserves behavior.

Fixtures are authored directly as bytes, independently of the Lean codecs and
assemblers. Acceptance is tested separately from whether an optimization applies;
no byte-identity promise is imposed on a noncanonical input.
"""

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + bytes(payload)


def fixture(kind):
    function_type = bytes([0x60, 0, 1, 0x7F])
    if kind == "rec-singleton":
        function_type = bytes([0x4E, 1]) + function_type
    elif kind == "explicit-final-subtype":
        function_type = bytes([0x4F, 0]) + function_type

    tables = memories = elements = data = b""
    exports = [(b"run", 0)]
    observation = {}
    if kind in ["prefixed-nullable-table", "explicit-null-table", "explicit-zero-element"]:
        table = bytes([0x70, 0, 1])  # one nullable funcref slot
        if kind == "prefixed-nullable-table":
            table = bytes([0x63, 0x70, 0, 1])
        elif kind == "explicit-null-table":
            table = bytes([0x40, 0]) + table + bytes([0xD0, 0x70, 0x0B])
        tables = section(4, bytes([1]) + table)
        exports.append((b"table", 1))
        observation["table"] = "function" if kind == "explicit-zero-element" else "null"
        if kind == "explicit-zero-element":
            # Explicit table 0 and funcref type; the compact form would be kind 4.
            elements = section(9, [1, 6, 0, 0x41, 0, 0x0B, 0x70, 1, 0xD2, 0, 0x0B])
    elif kind in ["padded-memory-limit", "explicit-zero-data"]:
        # A valid nonminimal encoding of a one-page minimum in the first case.
        limit = bytes([0x81, 0]) if kind == "padded-memory-limit" else bytes([1])
        memories = section(5, bytes([1, 0]) + limit)
        exports.append((b"memory", 2))
        observation["memory"] = [120, 121, 122] if kind == "explicit-zero-data" else [0, 0, 0]
        if kind == "explicit-zero-data":
            # Kind 2 explicitly names memory 0; kind 0 would omit that index.
            data = section(11, [1, 2, 0, 0x41, 0, 0x0B, 3, 120, 121, 122])

    export_bytes = bytes([len(exports)])
    for name, tag in exports:
        export_bytes += bytes([len(name)]) + name + bytes([tag, 0])
    # A zero-count local group is legal and denotes the same locals as no groups.
    locals_ = bytes([1, 0, 0x7F]) if kind == "zero-local-group" else bytes([0])
    # The return anchors the existing guarded vacuum rewrite.
    body = locals_ + bytes([1, 0x41, 42, 0x0F, 0x0B])
    module = (b"\0asm\1\0\0\0"
              + section(1, bytes([1]) + function_type)
              + section(3, [1, 0]) + tables + memories
              + section(7, export_bytes) + elements
              + section(10, bytes([1, len(body)]) + body) + data)
    return module, observation


def main():
    driver = sys.argv[1:] or [".lake/build/bin/wasm-opt"]
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node with WebAssembly GC support is required")
    kinds = ["rec-singleton", "explicit-final-subtype", "padded-memory-limit",
             "prefixed-nullable-table", "explicit-null-table", "explicit-zero-element",
             "explicit-zero-data", "zero-local-group"]
    observations = []
    with tempfile.TemporaryDirectory(prefix="wasm-alternate-encodings-") as directory:
        root = Path(directory)
        for kind in kinds:
            original, expected = fixture(kind)
            source = root / f"{kind}.wasm"
            source.write_bytes(original)
            observations.append({"path": str(source), **expected})
            sizes = []
            for label, flags in [("none", []), ("vacuum", ["--vacuum"]), ("O2", ["-O2"])]:
                output = root / f"{kind}-{label}.wasm"
                checked = subprocess.run([*driver, str(source), "-o", str(output), *flags],
                                         capture_output=True, text=True, timeout=90)
                assert checked.returncode == 0, (kind, label, checked.returncode,
                                                 checked.stdout, checked.stderr)
                assert output.is_file(), (kind, label, "missing output")
                sizes.append(output.stat().st_size)
                observations.append({"path": str(output), **expected})
            assert sizes[1] < sizes[0], (kind, sizes, "vacuum did not remove the nop")

        checked = subprocess.run([node, "-e", """
const fs = require('fs');
for (const test of JSON.parse(process.argv[1])) {
  const bytes = fs.readFileSync(test.path);
  if (!WebAssembly.validate(bytes)) throw Error('invalid module: ' + test.path);
  const e = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports;
  for (let n = 0; n < 3; n++) {
    if (e.run() !== 42) throw Error('wrong result: ' + test.path);
    if (test.table === 'null' && (e.table.length !== 1 || e.table.get(0) !== null))
      throw Error('default table initialization lost: ' + test.path);
    if (test.table === 'function' && (e.table.length !== 1 || e.table.get(0)() !== 42))
      throw Error('element initialization lost: ' + test.path);
    if (test.memory) {
      const memory = new Uint8Array(e.memory.buffer);
      if (memory.length !== 65536 || test.memory.some((b, i) => memory[i] !== b))
        throw Error('memory/data initialization lost: ' + test.path);
    }
  }
}
""", json.dumps(observations)], capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, (checked.returncode, checked.stdout, checked.stderr)

    print("Eight independent alternate Core encodings passed selected wasm-opt with no passes, vacuum and -O2")
    print("Vacuum removed a nop in every case; Node checked repeated calls and table/memory initialization")


if __name__ == "__main__":
    main()
