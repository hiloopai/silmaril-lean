#!/usr/bin/env python3
"""Compare L/I switched payloads with pinned libbrotli byte and bit traces."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import random
import runpy
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
SWITCH = runpy.run_path(str(SCRIPTS / "brotli-insert-copy-switch/check.py"))
PIN, check, run, MAPS = SWITCH["PIN"], SWITCH["check"], SWITCH["run"], SWITCH["MAPS"]


def assemble():
    """Author two RFC 7932 compressed blocks independently of either decoder."""
    bits = SWITCH["Bits"]()
    bits.code("0")  # Standard window 16.
    for last in (False, True):
        bits.code("10" if last else "0")
        bits.integer(0, 2)
        bits.integer(10, 16)  # MLEN 11.
        if not last:
            bits.code("0")
        for symbols in ([0, 1], [0]):
            bits.code("1000")  # Two literal, then two insert-and-copy types.
            bits.simple(4, symbols)
            bits.simple(26, [0])
            bits.integer(0, 2)  # Initial run of one.
        bits.code("0")  # One distance type.
        bits.integer(0, 2)
        bits.integer(1, 4)  # NDIRECT 1.
        bits.integer(0, 2)
        bits.integer(1, 2)  # LSB6 for type 0 and MSB6 for type 1.
        bits.code("1000")  # Two literal trees.
        bits.code("0")  # No zero-run prefix.
        bits.simple(2, [0, 1])
        # Set two sparse entries. Type 1 selects tree 1 at context 16.
        for index in range(128):
            bits.integer(int(index in (63, 80)), 1)
        bits.code("00")  # No inverse MTF and one distance tree.
        bits.simple(256, [65, 67])
        bits.simple(256, [192, 224])
        bits.simple(704, [144])  # Insert two, copy two.
        bits.simple(704, [152])  # Insert three, copy two.
        bits.simple(65, [16])   # Explicit distance one.
        # First L switch within the two-literal command. Copy two 0xc0 bytes.
        bits.code("0" "1" "10" "0")
        # Switch I, carry the second literal of type 1, then switch L back.
        bits.code("00" "1" "0" "10" "01")
        # Switch I back and perform two L switches in a literal-only end.
        bits.code("00" "0" "00" "1" "1" "00" "0")
    return bits.pack()


def native(wire, reference, traced):
    rows = MAPS["native_trace"](wire, reference, traced)
    extent = 8 * len(wire)
    commands, literals, switches, payloads, rings = [], [], [], [], []
    block = -1
    for row in rows:
        kind, *values = row.split()
        values = list(map(int, values))
        if kind == "envelope":
            block += 1
            command = -1
        elif kind == "payload":
            payloads.append(extent - values[0])
        elif kind == "command_run":
            active = values
        elif kind == "command":
            command += 1
            literal = 0
            _, symbol, insert, _, _, _, after = values
            commands.append([block, command, *active, symbol, insert, extent - after])
        elif kind == "switch":
            category, symbol, previous, current, length, before, type_end, after = values
            switches.append([block, category, symbol, previous, current, length,
                             extent - before, extent - type_end, extent - after])
        elif kind == "switched_literal":
            literals.append([block, command, literal, *values[:-2], extent - values[-2], extent - values[-1]])
            literal += 1
        elif kind in ("back", "terminal_ring"):
            rings.append(values)
        elif kind == "envelope_end":
            end = extent - values[0]
    return commands, literals, switches, payloads, rings[-1], end


def lean_decode(work, wire, output, bit_cap):
    path = work / "wire.br"
    path.write_bytes(wire)
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", path, str(output), str(bit_cap))
    return json.loads(result.stdout)


def accepted(reference, traced, work):
    wire = assemble()
    extent = 8 * len(wire)
    plain = run(reference, "-d", "-c", data=wire).stdout
    commands, literals, switches, payloads, ring, end = native(wire, reference, traced)
    expected = {"output": list(plain), "ring": ring, "commands": commands, "literals": literals, "end": end}
    check(lean_decode(work, wire, len(plain), extent) == expected, "Lean output, run state, context and source bits")
    check(len(commands) == 6 and len(literals) == 14 and len(switches) == 12, "native command/literal/switch coverage")
    for block in range(2):
        rows = [row for row in literals if row[0] == block]
        check([row[3:7] for row in rows] == [[0, 1, 0, 0], [1, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 0],
                                             [0, 1, 0, 0], [1, 0, 0, 1], [0, 1, 0, 0]], "reset and carry L runs")
        check(rows[1][9:12] == [16, 1, 192] and rows[2][7:11] == [192, 192, 48, 0],
              "copied bytes change context and switch the selected tree within the same L type")
    first_l = next(row for row in switches if row[1] == 0)
    first_i = next(row for row in switches if row[1] == 1)
    truncated = wire[:-1]
    last_bad = next(row for row in literals if row[-2] == 8 * len(truncated))
    check(subprocess.run([reference, "-d", "-c"], input=truncated, capture_output=True).returncode != 0,
          "native decoder rejects the truncated late literal")
    controls = (
        ("L-count-cap", wire, len(plain), first_l[-2] + 1, 0, 0, 1, first_l[-2], "literal-length", "bitLimit"),
        ("L-code-cap", wire, len(plain), first_l[-1], 0, 0, 1, first_l[-1], "literal-code", "bitLimit"),
        ("I-count-cap", wire, len(plain), first_i[-2] + 1, 0, 1, None, first_i[-2], "insertCopy-length", "bitLimit"),
        ("bounds-before-literal", wire, 1, payloads[0], 0, 0, None, payloads[0], "bounds", "outputLimit"),
        ("late-literal-truncation", truncated, len(plain), extent, *last_bad[:3], last_bad[-2],
         "literal-code", "truncated"),
    )
    failures = {}
    for name, data, output, bits, block, command, literal, bit, kind, cause in controls:
        actual = lean_decode(work, data, output, bits)["failure"]
        check((actual["block"], actual["command"], actual["literal"], actual["bit"], actual["kind"]) ==
              (block, command, literal, bit, kind) and actual["cause"].rstrip(")").endswith("." + cause),
              f"{name}: {actual}")
        failures[name] = actual
        print(f"{name}: {kind} at bit {bit}, block {block}, command {command}, literal {literal}")
    print(f"Assembled L/I stream: {len(plain)} bytes, {len(commands)} commands, {len(literals)} literals, {len(switches)} switches")
    return {"wire_hex": wire.hex(), "sha256": sha256(wire).hexdigest(), "plain_hex": plain.hex(),
            "commands": commands, "literals": literals, "switches": switches, "ring": ring, "end": end,
            "failures": failures}


def unsupported(reference, traced, work):
    rng = random.Random(281)
    plain = b"".join(bytes(65 + 20 * (j % 3) + rng.randrange(j % 3 + 2) for _ in range(2048)) for j in range(6))
    distance = run(reference, "-q", "9", "-w", "18", "-c", data=plain).stdout
    rows = MAPS["native_trace"](distance, reference, traced)
    check([int(row.split()[2]) for row in rows if row.startswith("types ")][:3] == [1, 1, 2], "native D types")
    payload = 8 * len(distance) - int(next(row.split()[1] for row in rows if row.startswith("payload ")))
    distance_failure = lean_decode(work, distance, len(plain), 8 * len(distance))["failure"]
    check(distance_failure == {"block": 0, "command": 0, "literal": None, "bit": payload,
                               "kind": "distanceBlockTypes", "cause": None}, "typed D-switch rejection")

    plain = b"".join(f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
                     for i in range(99))
    dictionary = run(reference, "-q", "7", "-w", "18", "-c", data=plain).stdout
    rows = MAPS["native_trace"](dictionary, reference, traced)
    extent = len(dictionary) * 8
    start = extent - int(next(row.split()[1] for row in rows if row.startswith("distance_begin ")))
    _, _, _, _, d, size = next(row.split() for row in rows if row.startswith("distance_end "))
    word = int(next(row.split()[1] for row in rows if row.startswith("dictionary_id ")))
    dictionary_failure = lean_decode(work, dictionary, len(plain), extent)["failure"]
    check(dictionary_failure == {"block": 0, "command": 0, "literal": None, "bit": start,
                                 "kind": "dictionary", "cause": [int(d), int(size), word]},
          f"typed static dictionary rejection: {dictionary_failure}")
    print(f"Native D switching and dictionary rejected at bits {payload} and {start}")
    return {"distance": {"sha256": sha256(distance).hexdigest(), "failure": distance_failure},
            "dictionary": {"sha256": sha256(dictionary).hexdigest(), "failure": dictionary_failure}}


def collect(reference, traced, work):
    return {"libbrotli_commit": PIN, "provenance": "independently assembled RFC 7932 two-meta-block specimen",
            "assembled": accepted(reference, traced, work), "unsupported": unsupported(reference, traced, work)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-literal-switch-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        report = collect(reference, traced, work)
        check(report == json.loads((HERE / "fixtures.json").read_text()), "pinned literal-switch replay")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
