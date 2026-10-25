#!/usr/bin/env python3
"""Require real selected optimization beyond the historical whole-module profile.

The inputs are independently authored bytes, with valid extended i31 element
initializers unrelated to the exported function's removable nop. No-pass and
vacuum output checks separate input acceptance from actual optimization.
"""

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def fixture(mode, *, nop=True, invalid=False):
    body = (bytes([0]) + (bytes([1]) if nop else b"")
            + bytes([0x43, 0, 0, 0xC0, 0x7F, 0x43, 0, 0, 0, 0, 0x92, 0x0B]))
    initializer = bytes([0x43, 0, 0, 0, 0]) if invalid else bytes([0x41, 7])
    element = (bytes([1, mode])
               + (bytes([0, 0x41, 0, 0x0B]) if mode == 6 else b"")
               + bytes([0x64, 0x6C, 1]) + initializer + bytes([0xFB, 0x1C, 0x0B]))
    return (b"\0asm\1\0\0\0"
            + section(1, bytes([1, 0x60, 0, 1, 0x7D]))
            + section(3, bytes([1, 0]))
            + section(4, bytes([1, 0x6C, 0, 1]))
            + section(7, bytes([1, 3]) + b"run" + bytes([0, 0]))
            + section(9, element)
            + section(10, bytes([1, len(body)]) + body))


def main():
    driver = sys.argv[1:] or [".lake/build/bin/wasm-opt"]
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node with GC and extended-constant support is required")

    with tempfile.TemporaryDirectory(prefix="wasm-selected-extended-") as directory:
        root = Path(directory)
        valid_paths = []
        for mode in [5, 7, 6]:
            source = root / f"element-{mode}.wasm"
            original = fixture(mode)
            source.write_bytes(original)
            valid_paths.append(source)
            for name, flags in [("empty", []), ("vacuum", ["--vacuum"]),
                                ("O2", ["-O2"])]:
                output = root / f"element-{mode}-{name}.wasm"
                checked = subprocess.run([*driver, str(source), *flags, "-o", str(output)],
                                         capture_output=True, text=True, timeout=90)
                assert checked.returncode == 0, (name, checked.stdout, checked.stderr)
                result = output.read_bytes()
                if name == "empty":
                    assert result == original, "no-pass input acceptance changed the fixture"
                elif name == "vacuum":
                    assert result == fixture(mode, nop=False), "vacuum failed to remove the actual nop"
                else:
                    assert len(result) < len(original), "O2 made no reduction beyond the old profile"
                valid_paths.append(output)

        invalid = root / "invalid-element.wasm"
        invalid.write_bytes(fixture(5, invalid=True))
        for name, flags in [("empty", []), ("vacuum", ["--vacuum"]), ("O2", ["-O2"])]:
            output = root / f"invalid-{name}.wasm"
            checked = subprocess.run([*driver, str(invalid), *flags, "-o", str(output)],
                                     capture_output=True, text=True, timeout=90)
            assert checked.returncode != 0, "invalid ref.i31 operand passed Core validation"
            assert "validation" in checked.stderr.lower(), checked.stderr
            assert not output.exists(), "invalid module produced an output artifact"

        checked = subprocess.run([node, "-e", """
const fs = require('fs');
const [invalid, ...valid] = process.argv.slice(1);
if (WebAssembly.validate(fs.readFileSync(invalid))) throw Error('invalid element accepted');
for (const path of valid) {
  const bytes = fs.readFileSync(path);
  if (!WebAssembly.validate(bytes)) throw Error('invalid output: ' + path);
  const run = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports.run;
  for (let i = 0; i < 3; i++) if (!Number.isNaN(run())) throw Error('lost NaN: ' + path);
}
""", str(invalid), *map(str, valid_paths)], capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, (checked.stdout, checked.stderr)

    print("Selected no-pass, vacuum and O2 passed all three extended-i31 element modes")
    print("Exact nop removal, invalid-input rejection and repeated independent Node observations passed")


if __name__ == "__main__":
    main()
