#!/usr/bin/env python3
"""Actual identity-leaf inlining after f32 sqrt, with independent wire/Node checks.

The fixture is hand-encoded, without either Lean or upstream assembly. This
checks a changing restricted inliner and its CLI selection, not full Binaryen
inlining algorithm, preset coverage, or NaN payload identity.
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


def fixture(*, extra_gc_type=False, element_mode=None):
    # One shared (f32)->f32 type. Function 0 is the identity local.get 0;
    # exported function 1 is local.get 0; f32.sqrt; call 0. Arithmetic is in
    # the caller: the unchanged callee effects guard does not admit sqrt.
    leaf = bytes([0, 0x20, 0, 0x0B])
    caller = bytes([0, 0x20, 0, 0x91, 0x10, 0, 0x0B])
    types = bytes([2 if extra_gc_type else 1, 0x60, 1, 0x7D, 1, 0x7D])
    if extra_gc_type:
        # Unused (func (param (ref null i31))), outside the legacy inliner
        # type-section whitelist. The numeric callee/caller remain unchanged.
        types += bytes([0x60, 1, 0x6C, 0])
    tables = section(4, bytes([1, 0x6C, 0, 1])) if element_mode is not None else b""
    elements = b""
    if element_mode is not None:
        element = (bytes([1, element_mode])
                   + (bytes([0, 0x41, 0, 0x0B]) if element_mode == 6 else b"")
                   + bytes([0x64, 0x6C, 1, 0x41, 7, 0xFB, 0x1C, 0x0B]))
        elements = section(9, element)
    return (HEADER
            + section(1, types)
            + section(3, bytes([2, 0, 0]))
            + tables
            + section(7, bytes([1, 3]) + b"run" + bytes([0, 1]))
            + elements
            + section(10, bytes([2, len(leaf)]) + leaf + bytes([len(caller)]) + caller))


def read_leb(data, pos):
    """Read enough unsigned/signed LEB syntax to skip the fixture's immediates."""
    value, shift = 0, 0
    for _ in range(5):
        assert pos < len(data), "truncated fixture immediate"
        byte = data[pos]
        pos += 1
        value |= (byte & 0x7F) << shift
        if byte < 0x80:
            return value, pos
        shift += 7
    raise AssertionError("fixture immediate exceeds five bytes")


def gc_signature_fixture():
    # The eligible identity leaf itself has (ref null i31)->(ref null i31).
    # A numeric exported caller constructs/extracts i31, so JS can invoke it.
    leaf = bytes([0, 0x20, 0, 0x0B])
    caller = bytes([0, 0x20, 0, 0xFB, 0x1C, 0x10, 0, 0xFB, 0x1D, 0x0B])
    return (HEADER
            + section(1, bytes([2, 0x60, 1, 0x6C, 1, 0x6C, 0x60, 1, 0x7F, 1, 0x7F]))
            + section(3, bytes([2, 0, 1]))
            + section(7, bytes([1, 3]) + b"run" + bytes([0, 1]))
            + section(10, bytes([2, len(leaf)]) + leaf + bytes([len(caller)]) + caller))


def function_opcodes(binary):
    """Read code opcodes independently, rejecting shapes outside this tiny test.

    Skipping immediate bytes avoids mistaking a local/type index for call 0.
    This is an inspection aid; Node below supplies independent full validation.
    """
    assert binary[:8] == HEADER
    pos = 8
    while pos < len(binary):
        tag = binary[pos]
        size, start = read_leb(binary, pos + 1)
        end = start + size
        assert end <= len(binary)
        pos = end
        if tag != 10:
            continue
        count, at = read_leb(binary, start)
        functions = []
        for _ in range(count):
            size, at = read_leb(binary, at)
            body_end = at + size
            assert body_end <= end
            groups, at = read_leb(binary, at)
            for _ in range(groups):
                _, at = read_leb(binary, at)
                assert binary[at] in [0x7D, 0x6C], "expected only f32 or nullable i31 locals"
                at += 1
            ops = []
            while at < body_end:
                op = binary[at]
                at += 1
                ops.append(op)
                if op in [0x02, 0x03, 0x04, 0x0C, 0x0D, 0x10, 0x20, 0x21, 0x22]:
                    _, at = read_leb(binary, at)
                elif op == 0xFB:
                    subop, at = read_leb(binary, at)
                    assert subop in [0x1C, 0x1D], "expected ref.i31 or i31.get_s"
                else:
                    assert op in [0x00, 0x01, 0x05, 0x0B, 0x0F, 0x1A, 0x91], hex(op)
                assert at <= body_end
            functions.append(ops)
        assert at == end
        return functions
    raise AssertionError("no code section")


def check_node(node, paths):
    checked = subprocess.run([node, "-e", """
const fs = require('fs');
for (const path of process.argv.slice(1)) {
  const bytes = fs.readFileSync(path);
  if (!WebAssembly.validate(bytes)) throw Error('invalid module: ' + path);
  const run = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports.run;
  for (let repeat = 0; repeat < 3; repeat++) {
    if (!Number.isNaN(run(-1))) throw Error('sqrt(-1) must be NaN: ' + path);
    if (run(4) !== 2) throw Error('sqrt(4) must be 2: ' + path);
    if (!Object.is(run(-0), -0)) throw Error('sqrt(-0) must retain its sign: ' + path);
    if (run(Infinity) !== Infinity) throw Error('sqrt(infinity) changed: ' + path);
  }
}
""", *map(str, paths)], capture_output=True, text=True, timeout=30)
    assert checked.returncode == 0, (checked.returncode, checked.stdout, checked.stderr)


def main():
    driver = sys.argv[1:] or [".lake/build/bin/wasm-opt"]
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node is required for independent validation and execution")

    def succeeds(*args):
        result = subprocess.run([*driver, *map(str, args)], capture_output=True,
                                text=True, timeout=90)
        assert result.returncode == 0, (args, result.returncode, result.stdout, result.stderr)
        return result

    def pipeline(*flags):
        report = succeeds(*flags, "--print-pipeline").stdout
        assert "no files read or written" in report
        return next(line[len("passes: "):] for line in report.splitlines()
                    if line.startswith("passes: ")).split(",")

    assert pipeline("--inlining", "--vacuum", "--inlining") == ["inlining", "vacuum", "inlining"]
    assert pipeline("--passes=inlining", "--dce") == ["inlining", "dce"]
    for preset in ["-O2", "-O3"]:
        expanded = pipeline(preset)
        assert "inlining" in expanded, preset
        assert pipeline("--inlining", preset, "--vacuum") == ["inlining", *expanded, "vacuum"]
    coverage = succeeds("--print-presets").stdout
    assert "inlining-optimizing" in coverage and "guarded small/leaf-callee inlining" in coverage

    with tempfile.TemporaryDirectory(prefix="wasm-selected-inlining-") as tmp:
        root = Path(tmp)
        source, output = root / "source.wasm", root / "output.wasm"
        original = fixture()
        source.write_bytes(original)
        assert [ops.count(0x10) for ops in function_opcodes(original)] == [0, 1]
        check_node(node, [source])
        succeeds(source, "-o", output)
        assert output.read_bytes() == original, "no-pass default changed canonical input"

        optimized = None
        paths = [source]
        for mode in ["equivalence", "refinement", "trap-insertion"]:
            succeeds(source, "-o", output, "--inlining", "--mode", mode, "--rounds", 0)
            assert output.read_bytes() == original, (mode, "zero rounds changed input")
            converted = root / (mode + ".wasm")
            succeeds(source, "-o", converted, "--inlining", "--mode", mode)
            actual = converted.read_bytes()
            assert actual != original, (mode, "selected inlining did not change bytes")
            ops = function_opcodes(actual)
            assert [body.count(0x10) for body in ops] == [0, 0], "direct call survived"
            assert [body.count(0x91) for body in ops] == [0, 1], "caller sqrt was lost or duplicated"
            if optimized is None:
                optimized = actual
            else:
                assert actual == optimized, "policy alone changed exact selected inlining"
            paths.append(converted)
        check_node(node, paths)

        # Whole-module type/output whitelists must not suppress the same
        # proved numeric leaf rewrite beside unrelated GC syntax.
        broader_paths = []
        for label, extra_gc_type, element_mode in [
                ("gc-type", True, None), ("extended-element", False, 5),
                ("combined-passive", True, 5), ("combined-declarative", True, 7),
                ("combined-active", True, 6)]:
            source = root / f"{label}-source.wasm"
            original = fixture(extra_gc_type=extra_gc_type, element_mode=element_mode)
            source.write_bytes(original)
            output = root / f"{label}-empty.wasm"
            succeeds(source, "-o", output)
            assert output.read_bytes() == original, (label, "no-pass input changed")
            broader_paths.extend([source, output])
            output = root / f"{label}-inline.wasm"
            succeeds(source, "-o", output, "--inlining")
            assert [body.count(0x10) for body in function_opcodes(output.read_bytes())] == [0, 0], (
                label, "unrelated module syntax suppressed actual inlining")
            assert [body.count(0x91) for body in function_opcodes(output.read_bytes())] == [0, 1]
            broader_paths.append(output)
        check_node(node, broader_paths)

        gc_source, gc_output = root / "gc-signature.wasm", root / "gc-signature-inline.wasm"
        gc_source.write_bytes(gc_signature_fixture())
        succeeds(gc_source, "-o", gc_output, "--inlining")
        assert [body.count(0x10) for body in function_opcodes(gc_output.read_bytes())] == [0, 0]
        checked = subprocess.run([node, "-e", """
const fs = require('fs');
for (const path of process.argv.slice(1)) {
  const bytes = fs.readFileSync(path);
  if (!WebAssembly.validate(bytes)) throw Error('invalid GC-signature module: ' + path);
  const run = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports.run;
  for (let repeat = 0; repeat < 3; repeat++) {
    for (const n of [0, 1, -1, 0x3fffffff, 0x40000000, 0x7fffffff, 0xffffffff]) {
      if (run(n) !== ((n << 1) >> 1)) throw Error('changed i31 roundtrip: ' + path);
    }
  }
}
""", str(gc_source), str(gc_output)], capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, (checked.stdout, checked.stderr)

    print("Selected identity-leaf inlining after f32 sqrt changed real bytes and removed the direct call")
    print("No-pass/zero-round identity, all-mode equality, ordered selection and O2/O3 inclusion passed")
    print("Node independently validated original/outputs and checked repeated NaN, 2, -0 and infinity results")
    print("Inlining also removed real calls beside unrelated GC types and all three extended-i31 element modes")
    print("An actual GC-reference-signature identity callee was inlined; Node checked signed-i31 boundary values")


if __name__ == "__main__":
    main()
