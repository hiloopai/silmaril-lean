"""Assemble the example blocks and export their LibVEX lifts without rewrites."""

import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import re
import subprocess
import tempfile

import archinfo
import pyvex


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BASE = 0x1000
FIXTURES = ("mov", "add", "je", "jne")


def width(ty):
    match = re.fullmatch(r"Ity_I(\d+)", ty)
    if match is None:
        raise ValueError(f"non-integer type: {ty}")
    return int(match[1])


def lean_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def expr(value):
    match value:
        case pyvex.expr.Const(con=con):
            return f".const {width(con.type)} {con.value:#x}"
        case pyvex.expr.Get(offset=offset, ty=ty):
            return f".get {offset} {width(ty)}"
        case pyvex.expr.RdTmp(tmp=tmp):
            return f".tmp {tmp}"
        case (pyvex.expr.Unop() | pyvex.expr.Binop() | pyvex.expr.Triop() | pyvex.expr.Qop()):
            return f".op {json.dumps(value.op)} {lean_list(map(expr, value.args))}"
        case _:
            raise ValueError(f"unhandled expression: {value.tag}: {value}")


def stmt(value):
    match value:
        case pyvex.stmt.IMark(addr=address, len=length, delta=delta):
            return f".mark {address:#x} {length} {delta}"
        case pyvex.stmt.WrTmp(tmp=tmp, data=data):
            return f".wrTmp {tmp} ({expr(data)})"
        case pyvex.stmt.Put(offset=offset, data=data):
            return f".put {offset} ({expr(data)})"
        case pyvex.stmt.Exit(guard=guard, dst=dst, jk=kind, offsIP=ip):
            if dst.type != "Ity_I64":
                raise ValueError(f"non-I64 exit: {dst}")
            return f".exit ({expr(guard)}) {dst.value:#x} {json.dumps(kind)} {ip}"
        case _:
            raise ValueError(f"unhandled statement: {value.tag}: {value}")


def tool(*argv, cwd=None):
    return subprocess.check_output(argv, text=True, cwd=cwd)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def render(work):
    for line in (HERE / "requirements.txt").read_text().splitlines():
        requirement = line.split()[0]
        package, version = requirement.split("==")
        if importlib.metadata.version(package) != version:
            raise ValueError(f"expected {requirement}")

    tool("as", "--64", "-o", "blocks.o", str(HERE / "blocks.s"), cwd=work)
    arch = archinfo.ArchAMD64()
    lean = ["module", "", "public import Silmaril.Machine.Vex.Scalar.Defs", "",
            "@[expose] public section", "", "namespace Silmaril.Machine.Vex.Fixtures", ""]
    report = ["# AMD64Scalar lift provenance", "",
              f"Assembler: `{tool('as', '--version').splitlines()[0]}`.",
              "Lifter: `pyvex==9.2.179` / `archinfo==9.2.179`, `ArchAMD64()`,",
              "`opt_level=1`, `strict_block_end=True`, `max_bytes=len(section)`, base `0x1000`.",
              "Input: raw `.text.*` sections of `blocks.s` (not linked programs).", ""]
    for name in FIXTURES:
        binary = f"{name}.bin"
        tool("objcopy", "-j", f".text.{name}", "-O", "binary", "blocks.o", binary, cwd=work)
        data = (work / binary).read_bytes()
        block = pyvex.IRSB(data, BASE, arch, max_bytes=len(data), opt_level=1, strict_block_end=True)
        if block.size != len(data):
            raise ValueError(f"{name}: not all bytes lifted")

        lean += [f"def {name}Bytes : List UInt8 := {lean_list(f'{byte:#04x}' for byte in data)}", "",
                 f"def {name}Lift : Raw.Block where", f"  address := {block.addr:#x}",
                 f"  types := {lean_list(map(width, block.tyenv.types))}", "  statements := ["]
        if block.statements:
            lean += [",\n".join(f"    {stmt(value)}" for value in block.statements)]
        lean += ["  ]", f"  next := {expr(block.next)}", f"  jumpKind := {json.dumps(block.jumpkind)}",
                 f"  ipOffset := {block.offsIP}", ""]

        disassembly = tool("objdump", "-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel",
                           f"--adjust-vma={BASE}", binary, cwd=work)
        lift = str(block)
        report += [f"## {name}", "", f"Bytes: `{data.hex(' ')}`.",
                   f"Bytes SHA-256: `{digest(data)}`.",
                   f"IRSB text (without trailing newline) SHA-256: `{digest(lift.encode())}`.", "",
                   "```text", *(line for line in disassembly.splitlines() if re.match(r"^\s+[0-9a-f]+:", line)),
                   "```", "", "```text", lift, "```", ""]

    lean += ["end Silmaril.Machine.Vex.Fixtures", ""]
    return {"Silmaril/Machine/Vex/Examples/Defs.lean": "\n".join(lean), "examples/vex/lifts.md": "\n".join(report)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output-root", type=Path, default=ROOT)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as work:
        artifacts = render(Path(work))
    for name, text in artifacts.items():
        path = args.output_root / name
        if args.check:
            if path.read_text() != text:
                raise SystemExit(f"stale fixture: {name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        print(name)


if __name__ == "__main__":
    main()
