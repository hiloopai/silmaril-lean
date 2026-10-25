#!/usr/bin/env python3
"""Independent original-wire tests for array backing and explicit atomic order.

No Node execution claim is made for Binaryen's experimental memory proposals.
The complete scalar table and all ordered access/ordering/index combinations
must emit metadata faithfully and independently reassemble and validate.
"""
import argparse
import re
import runpy
import shlex
import subprocess
import tempfile
from pathlib import Path

common = runpy.run_path(str(Path(__file__).with_name("test-atomic-disassembly.py")))
HEADER, uleb, section = common["HEADER"], common["uleb"], common["section"]


def array_module():
    names = ["i32.load", "i64.load", "f32.load", "f64.load", "i32.load8_s", "i32.load8_u",
             "i32.load16_s", "i32.load16_u", "i64.load8_s", "i64.load8_u", "i64.load16_s", "i64.load16_u",
             "i64.load32_s", "i64.load32_u", "i32.store", "i64.store", "f32.store", "f64.store",
             "i32.store8", "i32.store16", "i64.store8", "i64.store16", "i64.store32"]
    aligns = [2, 3, 2, 3, 0, 0, 1, 1, 0, 0, 1, 1, 2, 2, 2, 3, 2, 3, 0, 1, 0, 1, 2]
    names += ["v128.load", "v128.store"]
    # Array type0; function type1; no linear memory exists in this module.
    types = section(1, bytes([2, 0x5e, 0x78, 1, 0x60, 0, 0]))
    functions = section(3, bytes([1, 1]))
    instructions = bytes([2, 0x40, 0]) + b"".join(bytes([0x28 + i, 32 + align, 0, 0, 0]) for i, align in enumerate(aligns)) + bytes([0xfd, 0, 0x24, 0, 0, 0, 0xfd, 11, 0x24, 0, 0, 0, 0x0b])
    body = bytes([0]) + instructions + bytes([0x0b])
    return HEADER + types + functions + section(10, bytes([1]) + uleb(len(body)) + body), names


def ordered_instructions():
    ops = common["table"]()[3:]
    assert len(ops) == 63
    rows, names = [], []
    for memory in [0, 1]:
        for order, name in enumerate(["seqcst", "acqrel", "relaxed"]):
            for opcode, mnemonic, align in ops:
                code = order * 17 if opcode >= 0x1e else order
                rows.append(bytes([0xfe, opcode, 16 + 64 * memory + align]) + (bytes([memory]) if memory else b"") + bytes([code, 0, 0]))
                names.append((mnemonic, str(memory), name))
    return bytes([2, 0x40, 0]) + b"".join(rows) + bytes([0xfe, 3, 0, 0xfe, 3, 1, 0xfe, 3, 2, 0x0b]), names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dis-command", default=".lake/build/bin/wasm-dis-lean")
    parser.add_argument("--reference-as")
    parser.add_argument("--reference-opt")
    args = parser.parse_args()
    if bool(args.reference_as) != bool(args.reference_opt):
        parser.error("supply both --reference-as and --reference-opt")
    command = shlex.split(args.dis_command)
    array_bytes, array_names = array_module()
    ordered_body, ordered_names = ordered_instructions()
    ordered_bytes = common["module"](ordered_body, memories=bytes([2, 3, 1, 2, 7, 1, 2]))
    with tempfile.TemporaryDirectory(prefix="silmaril-memory-proposal-dis-") as directory:
        work = Path(directory)
        for name, original in [("array25", array_bytes), ("ordered378", ordered_bytes)]:
            source, output = work / (name + ".wasm"), work / (name + ".wat")
            source.write_bytes(original)
            subprocess.run(command + [str(source), "-o", str(output)], check=True)
            text = output.read_text()
            if name == "array25":
                seen = re.findall(r"(i(?:32|64)\.[\w]+|f(?:32|64)\.[\w]+|v128\.[\w]+)\s+\(type 0\)", text)
                assert seen == array_names, (seen, array_names)
                assert "(memory " not in text, text
            else:
                seen = re.findall(r"((?:i32|i64)\.atomic\.[\w.]+)\s+([01])\s+(seqcst|acqrel|relaxed)", text)
                assert seen == ordered_names, (len(seen), len(ordered_names), text)
                assert re.findall(r"atomic\.fence\s+(seqcst|acqrel|relaxed)", text) == ["seqcst", "acqrel", "relaxed"]
                assert "(memory i64 1 2 shared)" in text
            if args.reference_as:
                binary = work / (name + ".rebuilt.wasm")
                subprocess.run([args.reference_as, str(output), "--all-features", "--disable-compact-imports", "-o", str(binary)], check=True)
                subprocess.run([args.reference_opt, str(binary), "--all-features", "-o", str(work / (name + ".checked.wasm"))], check=True)
        # Invalid unknown/mismatched orders and forbidden array flag combinations.
        malformed = [common["module"](bytes([0xfe, 0x10, 0x12, 3, 0])),
                     common["module"](bytes([0xfe, 0x1e, 0x12, 1, 0])),
                     common["module"](bytes([0xfe, 3, 3])),
                     common["module"](bytes([0x28, 0x62, 0, 0, 0])),
                     common["module"](bytes([0x28, 0x32, 0, 0]))]
        for original in malformed:
            source, output = work / "bad.wasm", work / "untouched.wat"
            source.write_bytes(original)
            output.write_text("sentinel")
            result = subprocess.run(command + [str(source), "-o", str(output)], capture_output=True, text=True)
            assert result.returncode == 1, result
            assert output.read_text() == "sentinel"
            output.unlink()
            result = subprocess.run(command + [str(source), "-o", str(output)], capture_output=True, text=True)
            assert result.returncode == 1, result
            assert not output.exists()
    print("memory proposals: all 23 scalar and 2 full-width v128 array accesses and 378 ordered accesses; all 3 fence orders")
    print("upstream reassembly/validation: 2 passed" if args.reference_as else "upstream reassembly/validation: not requested")
    print("5 malformed/unsupported cases preserve output; no proposal execution claim")


if __name__ == "__main__":
    main()
