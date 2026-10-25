#!/usr/bin/env python3
"""Original atomic wire fixtures through the actual disassembler executable.

The independent table below generates every classic linear-memory atomic
opcode. Upstream reassembly and validation check emitted names and memargs;
Node executes a rebuilt shared-memory load/store/RMW/cmpxchg/wait/fence fixture.
"""
import argparse
import re
import shlex
import shutil
import subprocess
import tempfile
from pathlib import Path

HEADER = bytes.fromhex("0061736d01000000")


def uleb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    return bytes(out + bytes([n]))


def section(kind, body):
    return bytes([kind]) + uleb(len(body)) + body


def module(instructions, memories=bytes([1, 3, 1, 2]), result=False, exports=False):
    types = section(1, bytes([1, 0x60, 0, 1, 0x7f] if result else [1, 0x60, 0, 0]))
    functions = section(3, bytes([1, 0]))
    memory = section(5, memories)
    exported = section(7, bytes([2, 3, 109, 101, 109, 2, 0, 3, 114, 117, 110, 0, 0])) if exports else b""
    body = bytes([0]) + instructions + bytes([0x0b])
    return HEADER + types + functions + memory + exported + section(10, bytes([1]) + uleb(len(body)) + body)


def table():
    # value type, packed width suffix, unsigned suffix, alignment exponent
    shapes = [("i32", "", "", 2), ("i64", "", "", 3),
              ("i32", "8", "_u", 0), ("i32", "16", "_u", 1),
              ("i64", "8", "_u", 0), ("i64", "16", "_u", 1), ("i64", "32", "_u", 2)]
    rows = [(0, "memory.atomic.notify", 2), (1, "memory.atomic.wait32", 2),
            (2, "memory.atomic.wait64", 3)]
    for code, kind in [(0x10, "load"), (0x17, "store")]:
        for i, (value, packed, unsigned, align) in enumerate(shapes):
            rows.append((code + i, f"{value}.atomic.{kind}{packed}" + (unsigned if kind == "load" else ""), align))
    for op, name in enumerate(["add", "sub", "and", "or", "xor", "xchg", "cmpxchg"]):
        for i, (value, packed, unsigned, align) in enumerate(shapes):
            rows.append((0x1e + 7 * op + i, f"{value}.atomic.rmw{packed}.{name}{unsigned}", align))
    assert len(rows) == 66 and len({row[0] for row in rows}) == 66
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dis-command", default=".lake/build/bin/wasm-dis-lean")
    parser.add_argument("--reference-as")
    parser.add_argument("--reference-opt")
    args = parser.parse_args()
    if bool(args.reference_as) != bool(args.reference_opt):
        parser.error("supply both --reference-as and --reference-opt")
    command = shlex.split(args.dis_command)
    rows = table()
    all_ops = bytes([2, 0x40, 0]) + b"".join(bytes([0xfe, code, align, 0, 0]) for code, _, align in rows) + bytes([0xfe, 3, 0, 0x0b])
    # The final atomic load is the block's i32 result.
    run = bytes([2, 0x7f,
                 0x41, 0, 0x41, 42, 0xfe, 0x17, 2, 0,
                 0x41, 0, 0x41, 5, 0xfe, 0x1e, 2, 0, 0x1a,
                 0x41, 0, 0x41, 47, 0x41, 12, 0xfe, 0x48, 2, 0, 0x1a,
                 0x41, 0, 0x41, 13, 0x42, 0, 0xfe, 1, 2, 0, 0x1a,
                 0x41, 0, 0x41, 1, 0xfe, 0, 2, 0, 0x1a,
                 0xfe, 3, 0,
                 0x41, 0, 0xfe, 0x10, 2, 0, 0x0b])
    fixtures = {
        "all66": (module(all_ops), [name for _, name, _ in rows] + ["atomic.fence"], False),
        "runnable": (module(run, result=True, exports=True), ["shared", "i32.atomic.rmw.cmpxchg"], True),
        "pause": (module(bytes([0xfe, 4])), ["pause"], False),
        "memory64": (module(bytes([0, 0xfe, 0x10, 2, 0, 0]), memories=bytes([1, 7, 1, 2])), ["(memory i64 1 2 shared)", "i32.atomic.load"], False),
        "memory1": (module(bytes([0, 0xfe, 0x10, 0x42, 1, 0, 0]), memories=bytes([2, 3, 1, 2, 3, 1, 2])), ["i32.atomic.load 1"], False),
    }
    node_checks = 0
    with tempfile.TemporaryDirectory(prefix="silmaril-atomic-dis-") as directory:
        work = Path(directory)
        for name, (original, expected, executable) in fixtures.items():
            source, output = work / (name + ".wasm"), work / (name + ".wat")
            source.write_bytes(original)
            subprocess.run(command + [str(source), "-o", str(output)], check=True)
            text = output.read_text()
            for mnemonic in expected:
                assert mnemonic in text, (name, mnemonic, text)
            if name == "all66":
                seen = re.findall(r"(?<![\w.])(?:i(?:32|64)\.atomic\.[\w.]+|memory\.atomic\.[\w.]+|atomic\.fence)(?=\s|\))", text)
                assert seen == expected, (seen, expected)
            if args.reference_as:
                binary = work / (name + ".rebuilt.wasm")
                subprocess.run([args.reference_as, str(output), "--all-features", "--disable-compact-imports", "-o", str(binary)], check=True)
                subprocess.run([args.reference_opt, str(binary), "--all-features", "-o", str(work / (name + ".checked.wasm"))], check=True)
                if executable and shutil.which("node"):
                    subprocess.run(["node", "-e", '''
const fs = require("fs");
const instance = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])));
if (!(instance.exports.mem.buffer instanceof SharedArrayBuffer)) throw Error("lost shared flag");
if (instance.exports.run() !== 12) throw Error("wrong atomic execution result");
if (Atomics.load(new Int32Array(instance.exports.mem.buffer), 0) !== 12) throw Error("wrong memory contents");
''', str(binary)], check=True)
                    node_checks += 1
        malformed = [module(bytes([0xfe, 3, 3])), module(bytes([0xfe, 5])),
                     module(bytes([0xfe, 0x10, 2])), module(bytes([0xfe, 0x66, 0, 0])),
                     module(bytes([0xfe, 0x0f]))]
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
    print("atomic disassembly: all 66 memory opcodes, fence, pause, nested control, memory64 and memory index 1")
    print("upstream reassembly/validation: 5 passed" if args.reference_as else "upstream reassembly/validation: not requested")
    print(f"Node checked {node_checks} rebuilt load/store/RMW/cmpxchg/wait/notify/fence outputs")
    print("5 malformed/unsupported cases preserve existing output and create no new output")


if __name__ == "__main__":
    main()
