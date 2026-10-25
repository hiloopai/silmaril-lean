#!/usr/bin/env python3
"""Original legacy EH wire fixtures, upstream reassembly and actual execution.

Retains tagged handlers, final catch_all, delegate, rethrow, nesting and data
indices inside handlers. Node execution is attempted only for its legacy EH
support; proposal-memory execution is not implied by this suite.
"""
import argparse
import runpy
import shlex
import shutil
import subprocess
import tempfile
from pathlib import Path

common = runpy.run_path(str(Path(__file__).with_name("test-atomic-disassembly.py")))
HEADER, uleb, section = common["HEADER"], common["uleb"], common["section"]


def module(instructions, result=True, data=False):
    types = section(1, bytes([2, 0x60, 0, 0, 0x60, 0, 1, 0x7f] if result else [2, 0x60, 0, 0, 0x60, 0, 0]))
    functions = section(3, bytes([1, 1]))
    tags = section(13, bytes([2, 0, 0, 0, 0]))
    exports = section(7, bytes([1, 3, 114, 117, 110, 0, 0]))
    count = section(12, bytes([1])) if data else b""
    body = bytes([0]) + instructions + bytes([0x0b])
    code = section(10, bytes([1]) + uleb(len(body)) + body)
    payload = section(11, bytes([1, 1, 1, 42])) if data else b""
    return HEADER + types + functions + tags + exports + count + code + payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dis-command", default=".lake/build/bin/wasm-dis-lean")
    parser.add_argument("--reference-as")
    parser.add_argument("--reference-opt")
    args = parser.parse_args()
    if bool(args.reference_as) != bool(args.reference_opt):
        parser.error("supply both --reference-as and --reference-opt")
    command = shlex.split(args.dis_command)
    fixtures = {
        "tagged": (module(bytes([6, 0x7f, 8, 0, 7, 0, 0x41, 42, 0x0b])), ["(try", "(do", "(catch 0"], 42),
        "catch-all": (module(bytes([6, 0x7f, 8, 0, 0x19, 0x41, 43, 0x0b])), ["(catch_all"], 43),
        "multiple": (module(bytes([6, 0x7f, 8, 1, 7, 0, 0x41, 1, 7, 1, 0x41, 42, 0x0b])), ["(catch 0", "(catch 1"], 42),
        "delegate": (module(bytes([6, 0x7f, 6, 0x7f, 8, 0, 0x18, 0, 7, 0, 0x41, 42, 0x0b])), ["(delegate 0)", "(catch 0"], 42),
        "rethrow": (module(bytes([6, 0x7f, 6, 0x7f, 8, 0, 7, 0, 9, 0, 0x0b, 7, 0, 0x41, 42, 0x0b])), ["rethrow 0", "(catch 0"], 42),
        "data-in-catch": (module(bytes([6, 0x40, 8, 0, 7, 0, 0xfc, 9, 0, 0x0b]), result=False, data=True), ["data.drop 0", "(data"], None),
    }
    node_checks = 0
    with tempfile.TemporaryDirectory(prefix="silmaril-legacy-eh-dis-") as directory:
        work = Path(directory)
        for name, (original, expected, result) in fixtures.items():
            source, output = work / (name + ".wasm"), work / (name + ".wat")
            source.write_bytes(original)
            if args.reference_opt:
                subprocess.run([args.reference_opt, str(source), "--all-features", "-o", str(work / (name + ".original-checked.wasm"))], check=True)
            subprocess.run(command + [str(source), "-o", str(output)], check=True)
            text = output.read_text()
            for fragment in expected:
                assert fragment in text, (name, fragment, text)
            if args.reference_as:
                binary = work / (name + ".rebuilt.wasm")
                subprocess.run([args.reference_as, str(output), "--all-features", "--disable-compact-imports", "-o", str(binary)], check=True)
                subprocess.run([args.reference_opt, str(binary), "--all-features", "-o", str(work / (name + ".checked.wasm"))], check=True)
                if shutil.which("node"):
                    subprocess.run(["node", "-e", '''
const fs = require("fs");
const instance = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])));
const actual = instance.exports.run();
const expected = process.argv[2] === "none" ? undefined : Number(process.argv[2]);
if (actual !== expected) throw Error(`wrong handler result ${actual}, expected ${expected}`);
''', str(binary), "none" if result is None else str(result)], check=True)
                    node_checks += 1
        malformed = [module(bytes([7, 0]), result=False), module(bytes([6, 0x40, 0x19, 1, 0x19, 1, 0x0b]), result=False),
                     module(bytes([6, 0x40, 0x18]), result=False), module(bytes([6, 0x40, 7, 0, 0x18, 0, 0x0b]), result=False),
                     module(bytes([9]), result=False)]
        for original in malformed:
            source, output = work / "bad.wasm", work / "untouched.wat"
            source.write_bytes(original)
            output.write_text("sentinel")
            proc = subprocess.run(command + [str(source), "-o", str(output)], capture_output=True, text=True)
            assert proc.returncode == 1, proc
            assert output.read_text() == "sentinel"
            output.unlink()
            proc = subprocess.run(command + [str(source), "-o", str(output)], capture_output=True, text=True)
            assert proc.returncode == 1, proc
            assert not output.exists()
    print("legacy EH: 6 original wire fixtures accepted; tagged/multiple/final handlers, delegate, rethrow and handler data indices")
    print("upstream original validation/reassembly/validation: 6 passed" if args.reference_as else "upstream checks: not requested")
    print(f"Node checked {node_checks} rebuilt outputs; 5 malformed cases preserve output")


if __name__ == "__main__":
    main()
