#!/usr/bin/env python3
"""Compare the opt-in exact stream decoder with pinned libbrotli output."""
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
STREAM = runpy.run_path(str(SCRIPTS / "brotli-stream/check.py"))
PIN, check, run, MAPS = SWITCH["PIN"], SWITCH["check"], SWITCH["run"], SWITCH["MAPS"]


def compressed_header(bits, mlen, first_count, type_symbols, last, commands=(136, 2)):
    bits.code("10" if last else "0")
    bits.integer(0, 2)
    bits.integer(mlen - 1, 16)
    if not last:
        bits.code("0")  # The non-last block is compressed.
    SWITCH["payload_header"](bits, first_count, type_symbols, commands)


def assemble():
    """Assemble two independently initialized switched blocks and a metadata block."""
    bits = SWITCH["Bits"]()
    bits.code("0")  # Standard window 16.
    compressed_header(bits, 20, 2, [0, 1, 3], False)
    bits.code("01")
    for code, literal in (("10", ""), ("0", "0"), ("11", ""), ("10", "1")):
        bits.code(code)
        bits.integer(0, 2)
        bits.code(literal)

    note = b"tag"
    bits.code("0110")  # Non-last, metadata selector, reserved zero.
    bits.integer(1, 2)
    bits.integer(len(note) - 1, 8)
    bits.code("0" * (-len(bits.bits) % 8))
    for byte in note:
        bits.integer(byte, 8)

    compressed_header(bits, 14, 1, [0], True, (2, 136))
    # Initial type 0 copies from the previous block with its last distance.
    # Zero-bit previous-type switch to type 1 for two literal-plus-copy commands.
    bits.integer(1, 2)
    bits.code("01")
    bits.integer(0, 2)  # Zero-bit previous-type switch back to type 0.
    return bits.pack()


def native(wire, reference, traced):
    rows = MAPS["native_trace"](wire, reference, traced)
    extent = 8 * len(wire)
    blocks, ends, switches, commands, rings = [], [], [], [], []
    payloads = {}
    index = -1
    for row in rows:
        label, *values = row.split()
        values = list(map(int, values))
        if label == "envelope":
            index += 1
            count = 0
            blocks.append([*values[:-1], extent - values[-1]])
        elif label == "envelope_end":
            ends.append(extent - values[0])
        elif label == "payload":
            payloads[index] = extent - values[0]
        elif label == "switch":
            category, symbol, previous, current, length, before, after_type, after = values
            switches.append([index, count, category, symbol, previous, current, length,
                             extent - before, extent - after_type, extent - after])
        elif label == "command_run":
            active = values
        elif label == "command":
            current, symbol, insert, copy, mode, before, _ = values
            commands.append([index, count, *active, symbol, insert, copy, mode, extent - before])
            check(current == active[0], "native command uses active type")
            count += 1
        elif label in ("back", "terminal_ring"):
            rings.append(values)
    check(len(blocks) == len(ends), "native meta-block completion")
    return blocks, ends, switches, commands, payloads, rings[-1]


def lean_decode(work, wire, output, bits, blocks):
    path = work / "wire.br"
    path.write_bytes(wire)
    reply = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                HERE / "Interop.lean", path, str(output), str(bits), str(blocks))
    return json.loads(reply.stdout)


def compare_switched(reference, traced, work):
    wire = assemble()
    extent = 8 * len(wire)
    plain = run(reference, "-d", "-c", data=wire).stdout
    blocks, ends, switches, commands, payloads, ring = native(wire, reference, traced)
    check([row[:4] for row in blocks] == [[0, 0, 0, 20], [0, 1, 0, 3], [1, 0, 0, 14]],
          "native switched/metadata/switched envelope")
    check(plain[20:24] == b"BBBB", "second block uses previous bytes and distance ring")
    check([(row[0], row[2:5]) for row in commands if row[1] == 0] == [(0, [0, 1, 1]), (2, [0, 1, 0])],
          "both command histories initialize independently")
    check(len(commands) == 10 and len(switches) == 6, "native switched command counts")
    accepted = lean_decode(work, wire, len(plain), extent, 3)
    check(accepted["switched"] == {"output": list(plain), "ring": ring}, "whole-stream bytes and ring")
    check(accepted["legacy"]["cause"].endswith("Error.blockTypes)") and accepted["legacy"]["block"] == 0,
          "legacy whole stream still rejects the first switched header")
    late = next(row for row in switches if row[0] == 2)
    check(late[:7] == [2, 1, 1, 0, 0, 1, 2] and late[7] == payloads[2],
          "second block's implicit copy precedes its zero-bit switch")
    check(ends[-1] < extent, "native final padding extent")
    truncated = wire[:-1]
    check(len(truncated) * 8 == late[8], "missing byte starts at the late count")
    check(subprocess.run([reference, "-d", "-c"], input=truncated, capture_output=True).returncode != 0,
          "native truncation rejection")
    controls = (
        ("type-cap", wire, len(plain), switches[0][7] + 1, 3, "type", 0, 2, switches[0][7], "bitLimit"),
        ("late-length-cap", wire, len(plain), late[8] + 1, 3, "length", 2, 1, late[8], "bitLimit"),
        ("late-command-cap", wire, len(plain), late[9], 3, "execute", 2, 1, late[9], "bitLimit"),
        ("late-truncated-count", truncated, len(plain), extent, 3, "length", 2, 1, late[8], "truncated"),
        ("declared-output-cap", wire, len(plain) - 1, extent, 3, "envelope", 2, None, blocks[2][-1], "outputLimit"),
        ("block-cap", wire, len(plain), extent, 2, "envelope", 2, None, ends[1], "stepLimit"),
        ("final-bit-cap", wire, len(plain), extent - 1, 3, "envelope", 2, None, ends[-1], "bitLimit"),
        ("nonzero-fill", STREAM["flip_bit"](wire, ends[-1]), len(plain), extent, 3,
         "envelope", 2, None, ends[-1], "nonzeroPadding"),
        ("trailing", wire + b"\0", len(plain), extent + 8, 3, "envelope", 2, None, ends[-1], "trailingInput"),
    )
    failures = {}
    for name, data, output, bit_limit, block_cap, kind, block, cmd, bit, cause in controls:
        actual = lean_decode(work, data, output, bit_limit, block_cap)["switched"]
        check((actual.get("kind"), actual.get("block"), actual.get("command"), actual.get("bit")) ==
              (kind, block, cmd, bit) and actual["cause"].rstrip(")").endswith("." + cause), f"{name}: {actual}")
        failures[name] = actual
        print(f"{name}: {kind} at bit {bit}, block {block}, command {cmd}")
    print(f"Switched stream: {len(plain)} bytes, {len(commands)} commands, {len(switches)} switches, {len(blocks)} blocks")
    return {"wire_hex": wire.hex(), "sha256": sha256(wire).hexdigest(), "plain_hex": plain.hex(),
            "blocks": blocks, "ends": ends, "switches": switches, "commands": commands, "ring": ring,
            "failures": failures}


def compare_predecessors(source, reference, traced, work):
    cases = list(STREAM["EXECUTE"]["input_cases"](source, reference, work))
    cases.extend(STREAM["mixed_cases"](source, reference, work))
    pins = {}
    for name, data, wire, _ in cases:
        rows = MAPS["native_trace"](wire, reference, traced)
        count = sum(row.startswith("envelope ") for row in rows)
        pair = lean_decode(work, wire, len(data), len(wire) * 8, count)
        if name == "cli-dictionary":
            extent = 8 * len(wire)
            bit = extent - int(next(row.split()[-2] for row in rows if row.startswith("command ")))
            _, _, _, _, distance, size = next(row.split() for row in rows if row.startswith("distance_end "))
            word = int(next(row.split()[1] for row in rows if row.startswith("dictionary_id ")))
            check(pair["switched"] == {"kind": "dictionary", "bit": bit, "block": 0, "command": 0,
                                      "cause": [int(distance), int(size), word]}, "original dictionary error")
            check(pair["legacy"]["bit"] == bit and "unsupportedDictionary" in pair["legacy"]["cause"],
                  "legacy dictionary coordinates")
            pins[name] = {"sha256": sha256(wire).hexdigest(), "failure": pair["switched"]}
        else:
            *_, ring = native(wire, reference, traced)
            check(run(reference, "-d", "-c", data=wire).stdout == data, f"{name}: native producer output")
            expected = {"output": list(data), "ring": ring}
            check(pair["switched"] == pair["legacy"] == expected, f"{name}: both checked profiles and native")
            pins[name] = {"sha256": sha256(wire).hexdigest(), "output_sha256": sha256(data).hexdigest(), "ring": ring}
        print(f"{name}: predecessor comparison passed")
    return pins


def unsupported(reference, traced, work):
    pins = {}
    for category, chunk, quality, expected_types in (
        ("literal", 8192, 11, [3, 2, 2]),
        ("distance", 2048, 9, [1, 1, 2]),
    ):
        rng = random.Random(281)
        plain = b"".join(bytes(65 + 20 * (j % 3) + rng.randrange(j % 3 + 2)
                               for _ in range(chunk)) for j in range(6))
        wire = run(reference, "-q", str(quality), "-w", "18", "-c", data=plain).stdout
        rows = MAPS["native_trace"](wire, reference, traced)
        types = [int(row.split()[2]) for row in rows if row.startswith("types ")][:3]
        check(types == expected_types, f"native {category} switching control")
        payload = 8 * len(wire) - int(next(row.split()[1] for row in rows if row.startswith("payload ")))
        actual = lean_decode(work, wire, len(plain), 8 * len(wire), 1)["switched"]
        check(actual == {"kind": f"{category}BlockTypes", "bit": payload, "block": 0, "command": 0, "cause": None},
              f"original typed unsupported-{category} error")
        print(f"Native {category} switching rejected at payload bit {payload}")
        pins[category] = {"sha256": sha256(wire).hexdigest(), "types": types, "failure": actual}
    return pins


def collect(source, reference, traced, work):
    return {"libbrotli_commit": PIN, "switched": compare_switched(reference, traced, work),
            "predecessors": compare_predecessors(source, reference, traced, work),
            "unsupported": unsupported(reference, traced, work)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-switched-stream-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, SCRIPTS / "brotli-insert-copy-switch/trace-reference.py")
        report = collect(source, reference, traced, work)
        check(report == json.loads((HERE / "fixtures.json").read_text()), "pinned frames and localized errors")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
