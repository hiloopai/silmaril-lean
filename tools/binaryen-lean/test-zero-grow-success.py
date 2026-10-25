#!/usr/bin/env python3
"""Hand-encoded optional-trap removal fixtures, both widths, and Node checks.

Node checks the successful source execution and deterministic trap fallback. It
cannot force optional memory.grow failure: the actual source-failure witness and
its removal are proved in GrowZeroSuccessPass, not established by these runs.
"""

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


HEADER = b"\0asm\1\0\0\0"


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def name(text):
    encoded = text.encode()
    return bytes([len(encoded)]) + encoded


def fixture(width, kind="guarded", extra_export=False):
    """Construct actual wire bytes without Lean or upstream assembly."""
    value_type, const, eqz, memory_flags = {
        32: (0x7F, 0x41, 0x45, 0),
        64: (0x7E, 0x42, 0x50, 4),
    }[width]
    if kind == "guarded":
        # memory.grow 0; eqz; if (result iN) 0 else unreachable.
        instructions = bytes([const, 0, 0x40, 0, eqz, 4, value_type,
                              const, 0, 5, 0, 0x0B])
    elif kind == "success":
        instructions = bytes([const, 0])
    elif kind == "trap":
        instructions = bytes([0])
    else:
        raise AssertionError(kind)
    body = bytes([0]) + instructions + bytes([0x0B])
    exports = (bytes([3 if extra_export else 2])
               + name("grow") + bytes([0, 0])
               + name("memory") + bytes([2, 0])
               + (name("again") + bytes([0, 0]) if extra_export else b""))
    return (HEADER + section(1, bytes([1, 0x60, 0, 1, value_type]))
            + section(3, bytes([1, 0]))
            + section(5, bytes([1, memory_flags, 0]))
            + section(7, exports)
            + section(10, bytes([1, len(body)]) + body))


def check_node(node, path, width, traps=False, extra_export=False):
    checked = subprocess.run([node, "-e", """
const fs = require('fs');
const [path, width, traps, extra] = process.argv.slice(1);
const bytes = fs.readFileSync(path);
if (!WebAssembly.validate(bytes)) throw Error('invalid module: ' + path);
const e = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports;
const expected = extra === 'true' ? ['grow', 'memory', 'again'] : ['grow', 'memory'];
if (JSON.stringify(Object.keys(e)) !== JSON.stringify(expected))
  throw Error('exports changed: ' + path);
if (!(e.memory instanceof WebAssembly.Memory)) throw Error('memory missing');
const zero = width === '64' ? 0n : 0;
for (let repeat = 0; repeat < 3; repeat++) {
  if (traps === 'true') {
    let trapped = false;
    try { e.grow(); } catch (error) { trapped = error instanceof WebAssembly.RuntimeError; }
    if (!trapped) throw Error('deterministic trap was removed: ' + path);
  } else {
    if (e.grow() !== zero) throw Error('wrong result: ' + path);
    if (extra === 'true' && e.again() !== zero) throw Error('extra export changed');
  }
  if (e.memory.buffer.byteLength !== 0) throw Error('empty memory changed: ' + path);
}
""", str(path), str(width), str(traps).lower(), str(extra_export).lower()],
                             capture_output=True, text=True, timeout=30)
    assert checked.returncode == 0, (checked.returncode, checked.stdout, checked.stderr)


def main():
    driver = sys.argv[1:] or [".lake/build/bin/wasm-opt"]
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node is required for independent validation and execution")

    def call(*args):
        return subprocess.run([*driver, *map(str, args)], capture_output=True,
                              text=True, timeout=90)

    def succeeds(*args):
        result = call(*args)
        assert result.returncode == 0, (args, result.returncode, result.stdout, result.stderr)
        return result

    assert "--select-zero-grow-success" in succeeds("--help").stdout
    plan = succeeds("--select-zero-grow-success", "--mode", "refinement",
                    "--print-pipeline").stdout
    assert "no files read or written" in plan and "select-zero-grow-success: true" in plan

    with tempfile.TemporaryDirectory(prefix="wasm-zero-grow-success-") as tmp:
        root = Path(tmp)
        source, output = root / "source.wasm", root / "output.wasm"
        for width in [32, 64]:
            original = fixture(width)
            expected = fixture(width, "success")
            assert len(original) == 61 and len(expected) == 51
            source.write_bytes(original)
            check_node(node, source, width)
            succeeds(source, "-o", output)
            assert output.read_bytes() == original, "no-pass default changed canonical input"
            for mode in ["refinement", "trap-insertion"]:
                for rounds in [0, 2]:
                    succeeds(source, "-o", output, "--mode", mode,
                             "--select-zero-grow-success", "--rounds", rounds)
                    # Exact wire equality independently checks the sole constant-zero
                    # body, removal of grow/if/unreachable, retained memory and exports.
                    assert output.read_bytes() == expected, (width, mode, rounds)
                    check_node(node, output, width)

            for kind, extra in [("guarded", True), ("trap", False)]:
                original = fixture(width, kind, extra)
                source.write_bytes(original)
                check_node(node, source, width, kind == "trap", extra)
                for mode in ["refinement", "trap-insertion"]:
                    succeeds(source, "-o", output, "--mode", mode,
                             "--select-zero-grow-success")
                    assert output.read_bytes() == original, "unsupported full module lost identity fallback"
                    check_node(node, output, width, kind == "trap", extra)

        sentinel = b"existing output must survive policy rejection"
        invalid = [["--select-zero-grow-success"],
                   ["--mode", "equivalence", "--select-zero-grow-success"]]
        for mode in ["refinement", "trap-insertion"]:
            for other in ["--select-grow-failure", "--trap-grow-failure"]:
                for order in [["--select-zero-grow-success", other],
                              [other, "--select-zero-grow-success"]]:
                    invalid.append(["--mode", mode, *order])
        for flags in invalid:
            for exists in [False, True]:
                if exists:
                    output.write_bytes(sentinel)
                elif output.exists():
                    output.unlink()
                # A missing input distinguishes pure argument rejection (2)
                # from reading an input before checking the policies (1).
                rejected = call(root / "missing.wasm", "-o", output, *flags)
                assert rejected.returncode == 2, (flags, rejected.returncode, rejected.stderr)
                assert (output.read_bytes() == sentinel) if exists else not output.exists()
        output.write_bytes(sentinel)
        succeeds(root / "missing.wasm", "-o", output, "--select-zero-grow-success",
                 "--mode", "refinement", "--print-pipeline")
        assert output.read_bytes() == sentinel, "pipeline inspection performed IO"
        source.write_bytes(b"invalid wasm")
        rejected = call(source, "-o", output, "--mode", "refinement", "--select-zero-grow-success")
        assert rejected.returncode == 1 and output.read_bytes() == sentinel

    print("Both-width hand-encoded guarded modules changed from 61 to 51 bytes with memory/exports retained")
    print("No-pass identity, repeated zero returns/empty memory, and deterministic trap fallback checked in Node")
    print("Policy modes/conflicts reject before IO; optional source-failure/removal witness is supplied by Lean")


if __name__ == "__main__":
    main()
