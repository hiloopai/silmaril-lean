#!/usr/bin/env python3
"""Real-file selected-pass CLI checks, using independent wire bytes and Node."""

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


driver = sys.argv[1:] or [".lake/build/bin/wasm-opt"]
node = shutil.which("node")


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def fixture():
    # A valid i32 export with dead code after return. No assembler/encoder used.
    body = bytes([0, 0x41, 42, 0x0F, 0x01, 0x0B])
    return (b"\x00asm\x01\x00\x00\x00"
            + section(1, bytes([1, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([1, 0]))
            + section(7, bytes([1, 3]) + b"run" + bytes([0, 0]))
            + section(10, bytes([1, len(body)]) + body))


def deterministic_trap_fixture():
    # The i32 result is unreachable. The following constant can be deleted,
    # but the deterministic trap must not become a successful return.
    body = bytes([0, 0x00, 0x41, 42, 0x0B])
    return (b"\x00asm\x01\x00\x00\x00"
            + section(1, bytes([1, 0x60, 0, 1, 0x7F]))
            + section(3, bytes([1, 0]))
            + section(7, bytes([1, 3]) + b"run" + bytes([0, 0]))
            + section(10, bytes([1, len(body)]) + body))


def call(*args):
    return subprocess.run([*driver, *map(str, args)], text=True, capture_output=True, timeout=90)


def call_binary(*args, data=None):
    return subprocess.run([*driver, *map(str, args)], input=data, capture_output=True, timeout=90)


def succeeds(*args):
    result = call(*args)
    assert result.returncode == 0, (args, result.returncode, result.stdout, result.stderr)
    return result


def pipeline(*flags):
    report = succeeds(*flags, "--print-pipeline").stdout
    assert "no files read or written" in report
    return next(line[len("passes: "):] for line in report.splitlines() if line.startswith("passes: "))


for help_flag in ["-h", "--help"]:
    assert "No passes run by default" in succeeds(help_flag).stdout
listed = succeeds("--print-passes").stdout
assert "--dce" in listed and "--coalesce-locals" in listed
assert "--const-branch" not in listed and "Local subrules" in listed
presets = succeeds("--print-presets").stdout
assert "[omitted]" in presets and "restricted" in presets and "-Oz" in presets
assert pipeline() == ""
assert pipeline("--dce", "-O0", "--vacuum", "--dce") == "dce,vacuum,dce"
assert pipeline("--passes=const-branch,dce", "--vacuum") == "const-branch,dce,vacuum"
assert pipeline("-O") == pipeline("-Os")
assert pipeline("--dce", "-O2", "--vacuum") == "dce," + pipeline("-O2") + ",vacuum"
assert pipeline("-O2", "-O2") == pipeline("-O2") + "," + pipeline("-O2")
for flag in ["-O0", "-O1", "-O2", "-O3", "-O4", "-Os", "-Oz"]:
    pipeline(flag)

with tempfile.TemporaryDirectory(prefix="wasm-selected-opt-") as tmp:
    root = Path(tmp)
    original, output = root / "in.wasm", root / "out.wasm"
    original.write_bytes(fixture())
    succeeds(original, "-o", output)
    baseline = output.read_bytes()
    assert baseline == fixture(), "the no-pass default silently optimized this canonical fixture"
    succeeds("--coalesce-locals", "--output", output, original)
    assert output.read_bytes() == baseline, "coalesce-locals silently enabled other cleanup stages"
    succeeds("--dce", "-o", output, original)
    assert len(output.read_bytes()) < len(baseline), "the explicitly selected DCE did not run"
    optimized = output.read_bytes()
    for mode in ["equivalence", "refinement", "trap-insertion"]:
        succeeds(original, "-o", output, "--mode", mode, "--dce")
        assert output.read_bytes() == optimized, "the mode alone changed the selected exact pipeline"
    assert succeeds("--dce", original).stdout == "", "outputless conversion wrote binary output"
    streamed = call_binary("-", "--dce", "-o", "-", data=fixture())
    assert streamed.returncode == 0, streamed.stderr
    assert streamed.stdout == optimized, "stdin/stdout conversion differs from file conversion"
    streamed = call_binary(original, "--dce", "-o", "-")
    assert streamed.returncode == 0 and streamed.stdout == optimized, streamed.stderr
    streamed = call_binary("-", "--dce", "-o", output, data=fixture())
    assert streamed.returncode == 0 and output.read_bytes() == optimized, streamed.stderr
    streamed = call_binary("-", "--dce", data=fixture())
    assert streamed.returncode == 0 and streamed.stdout == b"", streamed.stderr
    if node:
        executed = subprocess.run([node, "-e", "const fs=require('fs');"
                                   "const b=fs.readFileSync(process.argv[1]);"
                                   "if(!WebAssembly.validate(b))process.exit(1);"
                                   "const i=new WebAssembly.Instance(new WebAssembly.Module(b));"
                                   "if(i.exports.run()!==42)process.exit(2);", str(output)],
                                  capture_output=True, text=True, timeout=30)
        assert executed.returncode == 0, executed.stderr
    for flag in ["-O", "-O0", "-O1", "-O2", "-O3", "-O4", "-Os", "-Oz"]:
        succeeds("-o", output, flag, original)

    original.write_bytes(deterministic_trap_fixture())
    succeeds(original, "-o", output, "--dce")
    trapping = output.read_bytes()
    for flags in [["--mode", "equivalence"],
                  ["--mode", "refinement", "--select-grow-failure"],
                  ["--mode", "trap-insertion", "--trap-grow-failure"]]:
        succeeds(original, "-o", output, "--dce", *flags)
        assert output.read_bytes() == trapping, "an inapplicable policy rewrote a deterministic trap"
    if node:
        checked = subprocess.run([node, "-e", """
const fs = require('fs');
const bytes = fs.readFileSync(process.argv[1]);
if (!WebAssembly.validate(bytes)) process.exit(1);
const run = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports.run;
for (let i = 0; i < 2; i++) {
  let trapped = false;
  try { run(); } catch (error) { trapped = error instanceof WebAssembly.RuntimeError; }
  if (!trapped) process.exit(2);
}
""", str(output)], capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, checked.stderr
    sentinel = b"existing output must survive"
    invalid = [["--unverified"], ["-O5"], ["--unknown"], ["--const-branch"],
               ["--passes="], ["--passes=dce,,vacuum"], ["--passes=not-a-pass"],
               ["--rounds", "-1"], ["--rounds"], ["--select-grow-failure"],
               ["--mode", "refinement", "--trap-grow-failure"]]
    for flags in invalid:
        args = [root / "missing.wasm", "-o", output, *flags]
        output.write_bytes(sentinel)
        rejected = call(*args)
        assert rejected.returncode == 2, (flags, rejected.returncode, rejected.stderr)
        assert output.read_bytes() == sentinel
        output.unlink()
        assert call(*args).returncode == 2 and not output.exists()
    output.write_bytes(sentinel)
    succeeds("--dce", "--print-pipeline", root / "missing.wasm", "-o", output)
    assert output.read_bytes() == sentinel, "pipeline inspection performed output IO"
    original.write_bytes(b"bad binary")
    assert call(original, "-o", output, "--dce").returncode == 1
    assert output.read_bytes() == sentinel
    assert call(original, "--dce").returncode == 1
    streamed = call_binary("-", "-o", "-", data=b"bad binary")
    assert streamed.returncode == 1 and streamed.stdout == b"", streamed.stderr

print("Selected pass order/repetitions/presets and no-IO pipeline inspection passed")
print("No-pass default and pass-only coalesce preserved; explicit DCE reduced real bytes")
print("Binary stdin/stdout, file/stream combinations and outputless conversion passed")
print("Correctness modes preserve the selected exact pipeline and deterministic trap fallback")
print("Rejected options/inputs preserved output; Node checked DCE output" if node else
      "Rejected options/inputs preserved output; Node unavailable")
