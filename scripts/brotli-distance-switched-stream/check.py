#!/usr/bin/env python3
"""Compare exact Brotli streams with all switches against pinned libbrotli."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import random
import runpy
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
BLOCK = runpy.run_path(str(SCRIPTS / "brotli-distance-switch-block/check.py"))
PIN, check, run, MAPS = BLOCK["PIN"], BLOCK["check"], BLOCK["run"], BLOCK["MAPS"]

STANDARD_MAX_WINDOW = (1 << 24) - 16

def aligned_bytes(bits, body):
    bits.code("0" * (-len(bits.bits) % 8))
    for byte in body:
        bits.integer(byte, 8)


def assemble_mixed(wire, end):
    """Prefix the independently assembled switched pair with raw and metadata blocks."""
    bits = BLOCK["COMMAND"]["SWITCH"]["Bits"]()
    bits.code("0000")  # Standard window 16, non-last, MLEN width 16.
    bits.integer(1, 16)  # Raw block of two bytes.
    bits.code("1")
    aligned_bytes(bits, b"xy")
    bits.code("0110")  # Non-last metadata, reserved zero.
    bits.integer(1, 2)
    bits.integer(2, 8)
    aligned_bytes(bits, b"tag")
    original = [byte >> index & 1 for byte in wire for index in range(8)]
    bits.bits.extend(original[1:end])
    return bits.pack()


def observe(wire, reference, traced):
    extent = 8 * len(wire)
    rows = MAPS["native_trace"](wire, reference, traced)
    blocks, ends, switches, rings = [], [], [], []
    types = []
    for row in rows:
        kind, *values = row.split()
        values = list(map(int, values))
        if kind == "envelope":
            blocks.append([*values[:-1], extent - values[-1]])
            command = -1
        elif kind == "types":
            types.append(values[1])
        elif kind == "command":
            command += 1
        elif kind == "switch":
            category, symbol, previous, current, length, before, type_end, end = values
            # A command switch precedes its command symbol. Literal and
            # distance switches follow the current command symbol.
            index = command + int(category == 1)
            switches.append([len(blocks) - 1, index, category, symbol, previous, current, length,
                             extent - before, extent - type_end, extent - end])
        elif kind in ("back", "terminal_ring"):
            rings.append(values)
        elif kind == "envelope_end":
            ends.append(extent - values[0])
    check(len(blocks) == len(ends) and blocks[-1][0] == 1, "exact native trace envelope")
    return {"blocks": blocks, "ends": ends, "switches": switches, "types": types,
            "ring": rings[-1], "dictionary": sum(row.startswith("dictionary_id ") for row in rows)}


def lean_decode(work, wire, output, bits, blocks, input_cap=None, window_cap=STANDARD_MAX_WINDOW):
    path = work / "wire.br"
    path.write_bytes(wire)
    reply = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                HERE / "Interop.lean", path, str(len(wire) if input_cap is None else input_cap),
                str(output), str(window_cap), str(bits), str(blocks))
    return json.loads(reply.stdout)


def compare(work, wire, plain, trace):
    check(trace["dictionary"] == 0, "dictionary-free accepted profile")
    actual = lean_decode(work, wire, len(plain), 8 * len(wire), len(trace["blocks"]))
    check(actual == {"output": list(plain), "ring": trace["ring"], "literalRefuses": True, "defaultRefuses": True},
          f"whole-stream bytes and ring or earlier profile refusal: {str(actual)[:600]}")


def native_cases(work, reference, traced):
    pins = {}
    for chunk, quality, types, categories in ((2048, 9, [1, 1, 2], [2]), (8192, 11, [3, 2, 2], [0, 1, 2])):
        rng = random.Random(281)
        plain = b"".join(bytes(65 + 20 * (j % 3) + rng.randrange(j % 3 + 2) for _ in range(chunk)) for j in range(6))
        wire = run(reference, "-q", str(quality), "-w", "18", "-c", data=plain).stdout
        check(run(reference, "-d", "-c", data=wire).stdout == plain, "native-produced bytes round trip")
        trace = observe(wire, reference, traced)
        counts = dict(sorted(Counter(row[2] for row in trace["switches"]).items()))
        check(trace["types"] == types and list(counts) == categories, "native-produced category switching")
        compare(work, wire, plain, trace)
        pins[str(quality)] = {"sha256": sha256(wire).hexdigest(), "output_sha256": sha256(plain).hexdigest(),
                              "output": len(plain), "blocks": trace["blocks"], "ends": trace["ends"],
                              "types": types, "switchCounts": [[category, count] for category, count in counts.items()],
                              "switchTraceSha256": sha256(json.dumps(trace["switches"]).encode()).hexdigest(),
                              "ring": trace["ring"]}
        print(f"Native quality {quality}: {len(plain)} bytes, types {types}, switch counts {counts}")
    return pins


def assembled_cases(work, reference, traced):
    single = BLOCK["COMMAND"]["assemble"]()
    _, first, _, _ = BLOCK["observe"](single, reference, traced)
    wire = BLOCK["assemble_pair"](single, first[0]["payload"], first[0]["end"])
    base_trace = observe(wire, reference, traced)
    mixed = assemble_mixed(wire, base_trace["ends"][-1])
    cases = (("switched pair", wire, base_trace, [[0, 0, 0, 17], [1, 0, 0, 21]]),
             ("raw / metadata / switched pair", mixed, observe(mixed, reference, traced),
              [[0, 0, 1, 2], [0, 1, 0, 3], [0, 0, 0, 17], [1, 0, 0, 21]]))
    pins = {}
    for name, source, trace, headers in cases:
        plain = run(reference, "-d", "-c", data=source).stdout
        check([row[:4] for row in trace["blocks"]] == headers and len(trace["switches"]) == 4,
              "independent assembled block shape")
        compare(work, source, plain, trace)
        pins[name] = {"wire_hex": source.hex(), "sha256": sha256(source).hexdigest(), "plain_hex": plain.hex(),
                      "blocks": trace["blocks"], "ends": trace["ends"], "switches": trace["switches"],
                      "ring": trace["ring"]}
        print(f"Assembled {name}: {len(plain)} bytes, {len(headers)} blocks, four D switches")
    check(bytes.fromhex(pins["raw / metadata / switched pair"]["plain_hex"]) ==
          b"xy" + bytes.fromhex(pins["switched pair"]["plain_hex"]), "raw output and metadata skip")
    plain = bytes.fromhex(pins["switched pair"]["plain_hex"])
    check(plain[17:21] == b"AAAA" and plain[13:17] != plain[17:21], "cross-block implicit distance 3")
    return pins, base_trace


def flip_bit(wire, bit):
    modified = bytearray(wire)
    modified[bit // 8] ^= 1 << (bit % 8)
    return bytes(modified)


def failures(work, reference, pins, trace):
    pair = pins["switched pair"]
    wire = bytes.fromhex(pair["wire_hex"])
    mixed = bytes.fromhex(pins["raw / metadata / switched pair"]["wire_hex"])
    end = trace["ends"][-1]
    extent = 8 * len(wire)
    late, last = trace["switches"][-2:]
    bad, padding, trailing = wire[:-1], flip_bit(wire, end), wire + b"\x00"
    for source in (bad, padding, trailing):
        check(subprocess.run([reference, "-d", "-c"], input=source, capture_output=True).returncode != 0,
              "native consumes one exact stream")
    # Each case supplies independent source offsets from the traced successful stream.
    cases = (
        ("late-type-cap", wire, 38, late[-3], 2, None, STANDARD_MAX_WINDOW,
         ("switch-type", 1, late[1], late[-3], "bitLimit")),
        ("late-count-cap", wire, 38, late[-2] + 1, 2, None, STANDARD_MAX_WINDOW,
         ("switch-length", 1, late[1], late[-2], "bitLimit")),
        ("late-symbol-cap", wire, 38, late[-1], 2, None, STANDARD_MAX_WINDOW,
         ("distance", 1, late[1], late[-1], "bitLimit")),
        ("late-truncation", bad, 38, extent, 2, None, STANDARD_MAX_WINDOW,
         ("switch-type", 1, last[1], last[-3], "truncated")),
        ("output-cap", wire, 37, extent, 2, None, STANDARD_MAX_WINDOW,
         ("envelope", 1, None, trace["blocks"][1][-1], "outputLimit")),
        ("block-cap", wire, 38, extent, 1, None, STANDARD_MAX_WINDOW,
         ("envelope", 1, None, trace["ends"][0], "stepLimit")),
        ("final-bit-cap", wire, 38, extent - 1, 2, None, STANDARD_MAX_WINDOW,
         ("envelope", 1, None, end, "bitLimit")),
        ("nonzero-padding", padding, 38, extent, 2, None, STANDARD_MAX_WINDOW,
         ("envelope", 1, None, end, "nonzeroPadding")),
        ("trailing-input", trailing, 38, extent + 8, 2, None, STANDARD_MAX_WINDOW,
         ("envelope", 1, None, end, "trailingInput")),
        ("raw-alignment", flip_bit(mixed, 21), 40, 8 * len(mixed), 4, None, STANDARD_MAX_WINDOW,
         ("envelope", 0, None, 21, "nonzeroPadding")),
        ("input-cap", wire, 38, extent, 2, len(wire) - 1, STANDARD_MAX_WINDOW,
         ("envelope", None, None, 0, "inputLimit")),
        ("window-cap", wire, 38, extent, 2, None, (1 << 16) - 17,
         ("envelope", None, None, 0, "windowLimit")),
    )
    pins = {}
    for name, source, output, bits, blocks, input_cap, window_cap, expected in cases:
        failure = lean_decode(work, source, output, bits, blocks, input_cap, window_cap)["failure"]
        actual = tuple(failure[key] for key in ("stage", "block", "command", "bit"))
        check((*actual, failure["cause"].rstrip(")").split(".")[-1]) == expected, f"{name}: {failure}")
        pins[name] = failure
        print(f"{name}: {failure['stage']} at original bit {failure['bit']}, block {failure['block']}")
    return pins


def dictionary_case(work, reference):
    plain = b"".join(f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
                     for i in range(99))
    wire = run(reference, "-q", "7", "-w", "18", "-c", data=plain).stdout
    prior = json.loads((SCRIPTS / "brotli-distance-switch-block/fixtures.json").read_text())["native_dictionary"]
    check(sha256(wire).hexdigest() == prior["sha256"], "pinned native dictionary stream")
    check(run(reference, "-d", "-c", data=wire).stdout == plain, "native dictionary materialization")
    failure = lean_decode(work, wire, len(plain), 8 * len(wire), 1)["failure"]
    check(failure == prior["failure"], f"whole-stream typed dictionary refusal: {failure}")
    print(f"Native dictionary rejected at original bit {failure['bit']}")
    return prior


def collect(work, reference, traced):
    native = native_cases(work, reference, traced)
    assembled, trace = assembled_cases(work, reference, traced)
    return {"libbrotli_commit": PIN, "native": native, "assembled": assembled,
            "failures": failures(work, reference, assembled, trace),
            "native_dictionary": dictionary_case(work, reference)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-distance-stream-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, SCRIPTS / "brotli-distance-switch/trace-reference.py")
        report = collect(work, reference, traced)
        check(report == json.loads((HERE / "fixtures.json").read_text()), "pinned exact whole-stream replay")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
