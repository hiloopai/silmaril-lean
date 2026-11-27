#!/usr/bin/env python3
"""Compare an independently assembled RFC 7932 I-switch stream with libbrotli."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import runpy
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
MAPS = runpy.run_path(str(SCRIPTS / "brotli-context-maps/check.py"))
PIN, check, run = MAPS["PIN"], MAPS["check"], MAPS["run"]


class Bits:
    def __init__(self):
        self.bits = []

    def integer(self, value, width):
        self.bits.extend((value >> i) & 1 for i in range(width))

    def code(self, pattern):
        self.bits.extend(map(int, pattern))

    def simple(self, alphabet, symbols):
        self.integer(1, 2)
        self.integer(len(symbols) - 1, 2)
        for symbol in symbols:
            self.integer(symbol, (alphabet - 1).bit_length())

    def pack(self):
        return bytes(sum(bit << i for i, bit in enumerate(self.bits[start:start + 8]))
                     for start in range(0, len(self.bits), 8))


def header(mlen, count, type_symbols):
    """Author the wire from the RFC fields. The native library supplies the oracle."""
    bits = Bits()
    bits.code("010")  # Window 16, ISLAST, ISLASTEMPTY=0.
    bits.integer(0, 2)
    bits.integer(mlen - 1, 16)
    bits.code("0")  # NBLTYPESL=1.
    bits.code("1000")  # NBLTYPESI=2.
    bits.simple(4, type_symbols)
    bits.simple(26, [0])  # Count code 0 has two extra bits and base one.
    bits.integer(count - 1, 2)
    bits.code("0")  # NBLTYPESD=1.
    bits.integer(0, 2)  # NPOSTFIX=0.
    bits.integer(1, 4)  # NDIRECT=1.
    bits.integer(0, 2)  # Literal context mode LSB6.
    bits.code("00")  # The two implicit one-tree context maps.
    bits.simple(256, [65, 66])  # A and B, one bit each.
    bits.simple(704, [136])  # Type 0 inserts one literal, then explicitly copies two.
    bits.simple(704, [2])  # Type 1 copies four using the last distance.
    bits.simple(65, [16])  # Explicit distance 1.
    return bits


def assemble():
    bits = header(20, 2, [0, 1, 3])  # Type code words 0, 10, 11.
    bits.code("01")  # The two initial commands insert A then B.
    for code, literal in (("10", ""), ("0", "0"), ("11", ""), ("10", "1")):
        bits.code(code)
        bits.integer(0, 2)  # Each switched run contains one command.
        bits.code(literal)
    return bits.pack()


def assemble_singleton():
    bits = header(14, 1, [0])  # A zero-bit previous-type symbol.
    bits.code("0")  # Initial command adds AAA.
    bits.integer(1, 2)  # Type 1 emits two copies of length four.
    bits.integer(0, 2)  # Type 0 has one command.
    bits.code("1")  # Final command adds BBB.
    return bits.pack()


def native(wire, reference, traced):
    extent = 8 * len(wire)
    plain = run(reference, "-d", "-c", data=wire).stdout
    rows = MAPS["native_trace"](wire, reference, traced)
    types = [int(row.split()[2]) for row in rows if row.startswith("types ")]
    check(types == [1, 2, 1], "native L/I/D type counts")
    events = []
    switches = []
    produced = 0
    for row in rows:
        label, *values = row.split()
        values = list(map(int, values))
        if label == "payload":
            start = extent - values[0]
        elif label == "switch":
            category, symbol, previous, current, length, before, after_type, after = values
            check(category == 1 and extent - before == start, "native switch at the command boundary")
            switches.append([symbol, previous, current, length, extent - before, extent - after_type, extent - after])
        elif label == "command_run":
            block_type, previous, remaining = values
        elif label == "command":
            current, symbol, insert, copy, _, before, _ = values
            check(current == block_type, "native command tree and active type")
            check((switches[-1][-1] if switches and switches[-1][-3] == start else start)
                  == extent - before, "native command begins after its switch")
        elif label == "distance_end":
            unread, position, _, distance, copied = values
            check(position == produced + insert and distance == 1 and copied == copy, "native output position")
            produced = position + copy
            stop = extent - unread
            events.append([start, stop, block_type, previous, remaining, symbol, produced])
            start = stop
    check(produced == len(plain), "native output and command extent")
    return plain, events, switches


def lean_decode(work, wire, output, bit_limit):
    path = work / "wire.br"
    path.write_bytes(wire)
    reply = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                HERE / "Interop.lean", path, str(output), str(bit_limit))
    return json.loads(reply.stdout)


def compare(wire, reference, traced, work, command_count, forms):
    plain, events, switches = native(wire, reference, traced)
    actual = lean_decode(work, wire, len(plain), len(wire) * 8)
    check(actual == {"output": list(plain), "commands": events, "end": events[-1][1], "failure": None},
          "Lean independently executed the complete assembled fixture")
    check(len(events) == command_count and [row[:4] for row in switches] == forms, "native switch forms and counts")
    print(f"assembled fixture: {len(plain)} bytes, {len(events)} commands, {len(switches)} switch prefixes")
    return {"wire_hex": wire.hex(), "sha256": sha256(wire).hexdigest(), "plain_hex": plain.hex(),
            "commands": events, "switches": switches}


def collect(reference, traced, work):
    wire = assemble()
    forms = [[1, 0, 1, 1], [0, 1, 0, 1], [3, 0, 1, 1], [1, 1, 0, 1]]
    mixed = compare(wire, reference, traced, work, 6, forms)
    singleton = compare(assemble_singleton(), reference, traced, work, 4, [[0, 0, 1, 2], [0, 1, 0, 1]])
    plain = bytes.fromhex(mixed["plain_hex"])
    events, switches = mixed["commands"], mixed["switches"]
    first_type, first_length, _ = switches[0][-3:]
    truncated = wire[:-1]
    truncated_at = switches[-2][-3]
    check(truncated_at + 1 == len(truncated) * 8, "truncation cuts the explicit type code")
    check(subprocess.run([reference, "-d", "-c"], input=truncated, capture_output=True).returncode != 0,
          "native decoder rejects the truncated type code")
    controls = (
        ("type-cap", wire, len(plain), first_type + 1, 2, "type", first_type, "bitLimit"),
        ("count-cap", wire, len(plain), first_length + 1, 2, "length", first_length, "bitLimit"),
        ("truncated-type", truncated, len(plain), len(wire) * 8, 4, "type", truncated_at, "truncated"),
        ("output-cap", wire, len(plain) - 1, len(wire) * 8, 5, "execute", switches[-1][-1], "outputLimit"),
    )
    failure_pins = {}
    for name, data, output, bits, passed, stage, offset, cause in controls:
        rejected = lean_decode(work, data, output, bits)
        failure = rejected["failure"]
        check(failure["stage"] == stage and failure["bit"] == offset and failure["cause"].endswith("." + cause),
              f"{name}: localized failure {failure}")
        if stage != "execute":
            check(failure["category"].endswith(".insertCopy"), f"{name}: command category")
        check(rejected["commands"] == events[:passed] and rejected["output"] == list(plain[:events[passed - 1][-1]]),
              f"{name}: prior commands only")
        failure_pins[name] = {"passed": passed, **failure}
        print(f"{name}: {stage} at original bit {offset} after {passed} accepted commands")
    return {
        "libbrotli_commit": PIN,
        "provenance": "independently assembled RFC 7932 streams, output and counters observed in libbrotli",
        "fixtures": {"four-forms": mixed, "singleton-previous": singleton}, "failures": failure_pins,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-switch-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        manifest = collect(reference, traced, work)
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "pinned switch output and trace")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
