#!/usr/bin/env python3
"""Run the exact stream entry point against pinned libbrotli full streams."""
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
LITERAL = runpy.run_path(str(SCRIPTS / "brotli-literal-switch/check.py"))
SWITCHED = runpy.run_path(str(SCRIPTS / "brotli-switched-stream/check.py"))
PIN, check, run, MAPS = LITERAL["PIN"], LITERAL["check"], LITERAL["run"], LITERAL["MAPS"]


def padded_body(bits, body):
    bits.code("0" * (-len(bits.bits) % 8))
    for byte in body:
        bits.integer(byte, 8)


def assemble_mixed(literal_wire, first_end, last_end):
    """Wrap the authored L/I blocks with raw, metadata and an implicit cross-block copy."""
    bits = LITERAL["SWITCH"]["Bits"]()
    bits.code("0")  # Standard window 16.
    bits.code("000")  # Non-last, MLEN selector zero.
    bits.integer(1, 16)
    bits.code("1")  # ISUNCOMPRESSED.
    padded_body(bits, b"xy")
    bits.code("0110")  # Non-last metadata, reserved zero.
    bits.integer(1, 2)
    bits.integer(2, 8)
    padded_body(bits, b"tag")

    original = [byte >> index & 1 for byte in literal_wire for index in range(8)]
    bits.bits.extend(original[1:first_end])
    check(original[first_end:first_end + 2] == [1, 0], "prior second block was last and nonempty")
    # Replace last/nonempty with non-last and append a clear ISUNCOMPRESSED.
    bits.bits.extend([0, *original[first_end + 2:first_end + 20], 0])
    bits.bits.extend(original[first_end + 20:last_end])

    bits.code("10")  # Last, nonempty, compressed.
    bits.integer(0, 2)
    bits.integer(3, 16)  # MLEN 4.
    bits.code("000")  # One type per category.
    bits.integer(0, 2)
    bits.integer(1, 4)  # One direct distance, unused here.
    bits.integer(0, 2)  # LSB6.
    bits.code("00")  # Implicit maps.
    bits.simple(256, [0])  # Unused literal singleton.
    bits.simple(704, [2])  # Zero-bit command: insert zero, copy four at recent distance.
    bits.simple(65, [16])   # Unused distance singleton.
    return bits.pack()


def lean_decode(work, wire, output, bits, blocks, input_limit=None):
    path = work / "wire.br"
    path.write_bytes(wire)
    reply = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                HERE / "Interop.lean", path, str(len(wire) if input_limit is None else input_limit),
                str(output), str(bits), str(blocks))
    return json.loads(reply.stdout)


def accepted(name, work, wire, reference, traced, types, previous=False):
    plain = run(reference, "-d", "-c", data=wire).stdout
    blocks, ends, switches, commands, payloads, ring = SWITCHED["native"](wire, reference, traced)
    check([row[:4] for row in blocks] == types, f"{name}: native meta-block framing")
    pair = lean_decode(work, wire, len(plain), 8 * len(wire), len(types))
    check(pair["current"] == {"output": list(plain), "ring": ring}, f"{name}: exact stream output and ring")
    if previous:
        check(pair["previous"] == pair["current"], f"{name}: previous opt-in profile")
    else:
        check("literalBlockTypes" in pair["previous"], f"{name}: previous profile rejects switched literals")
    print(f"{name}: {len(plain)} bytes, {len(types)} blocks, {len(commands)} commands, {len(switches)} switches")
    return {"wire_hex": wire.hex(), "sha256": sha256(wire).hexdigest(), "plain_hex": plain.hex(),
            "blocks": blocks, "ends": ends, "switches": switches, "ring": ring}, commands, payloads


def failures(work, reference, literal, mixed, mixed_payloads):
    wire = bytes.fromhex(literal["wire_hex"])
    mix = bytes.fromhex(mixed["wire_hex"])
    output = len(bytes.fromhex(literal["plain_hex"]))
    mix_output = len(bytes.fromhex(mixed["plain_hex"]))
    late = next(row for row in literal["switches"] if row[0] == 1 and row[2] == 0)
    late_i = next(row for row in literal["switches"] if row[0] == 1 and row[2] == 1)
    last_end = literal["ends"][-1]
    extent = 8 * len(wire)
    check(last_end < extent, "padding control needs terminal fill")
    bad_padding = SWITCHED["STREAM"]["flip_bit"](wire, last_end)
    for malformed in (wire[:-1], bad_padding, wire + b"\x00"):
        check(subprocess.run([reference, "-d", "-c"], input=malformed, capture_output=True).returncode != 0,
              "libbrotli rejects each malformed full stream")
    cases = (
        ("late-L-count-cap", wire, output, late[-2] + 1, 2, len(wire),
         ("literal-length", 1, 0, 1, late[-2], "bitLimit")),
        ("late-I-count-cap", wire, output, late_i[-2] + 1, 2, len(wire),
         ("insertCopy-length", 1, 1, None, late_i[-2], "bitLimit")),
        ("late-literal-truncation", wire[:-1], output, extent, 2, len(wire),
         ("literal-code", 1, 2, 0, 8 * len(wire[:-1]), "truncated")),
        ("final-padding-cap", wire, output, extent - 1, 2, len(wire),
         ("envelope", 1, None, None, last_end, "bitLimit")),
        ("nonzero-final-padding", bad_padding, output, extent, 2, len(wire),
         ("envelope", 1, None, None, last_end, "nonzeroPadding")),
        ("trailing-byte", wire + b"\x00", output, extent + 8, 2, len(wire) + 1,
         ("envelope", 1, None, None, last_end, "trailingInput")),
        ("cumulative-output-cap", mix, mix_output - 1, 8 * len(mix), 5, len(mix),
         ("envelope", 4, None, None, mixed["blocks"][4][-1], "outputLimit")),
        ("block-cap", mix, mix_output, 8 * len(mix), 4, len(mix),
         ("envelope", 4, None, None, mixed["ends"][3], "stepLimit")),
        ("cross-copy-header-cap", mix, mix_output, mixed_payloads[4] - 1, 5, len(mix),
         ("envelope", 4, None, None, mixed["blocks"][4][-1], "bitLimit")),
        ("input-cap", mix, mix_output, 8 * len(mix), 5, len(mix) - 1,
         ("envelope", None, None, None, 0, "inputLimit")),
    )
    results = {}
    for name, data, cap, bits, blocks, input_cap, expected in cases:
        actual = lean_decode(work, data, cap, bits, blocks, input_cap)["current"]
        found = tuple(actual.get(key) for key in ("kind", "block", "command", "literal", "bit"))
        found += (actual["cause"].rstrip(")").split(".")[-1],)
        check(found == expected, f"{name}: {actual}")
        print(f"{name}: {actual['kind']} at bit {actual['bit']}, block {actual['block']}")
        results[name] = actual
    return results


def unsupported(work, reference):
    prior = json.loads((SCRIPTS / "brotli-literal-switch/fixtures.json").read_text())["unsupported"]
    rng = random.Random(281)
    distance_plain = b"".join(bytes(65 + 20 * (j % 3) + rng.randrange(j % 3 + 2)
                                    for _ in range(2048)) for j in range(6))
    dictionary_plain = b"".join(f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
                                for i in range(99))
    cases = (("distance", "9", distance_plain), ("dictionary", "7", dictionary_plain))
    for name, quality, plain in cases:
        wire = run(reference, "-q", quality, "-w", "18", "-c", data=plain).stdout
        check(run(reference, "-d", "-c", data=wire).stdout == plain, f"{name}: native accepted control")
        expected = prior[name]
        check(sha256(wire).hexdigest() == expected["sha256"], f"{name}: prior native pin")
        failure = lean_decode(work, wire, len(plain), 8 * len(wire), 8)["current"]
        check(failure == expected["failure"], f"{name}: typed whole-stream failure {failure}")
        print(f"native {name} rejected at bit {failure['bit']} with the lower cause")
    return prior


def collect(work, reference, traced):
    literal_wire = LITERAL["assemble"]()
    literal, _, _ = accepted("L/I", work, literal_wire, reference, traced,
                             [[0, 0, 0, 11], [1, 0, 0, 11]])
    mix_wire = assemble_mixed(literal_wire, *literal["ends"])
    mixed, mix_commands, mixed_payloads = accepted(
        "raw/metadata/L-I/L-I/cross-copy", work, mix_wire, reference, traced,
        [[0, 0, 1, 2], [0, 1, 0, 3], [0, 0, 0, 11], [0, 0, 0, 11], [1, 0, 0, 4]])
    plain = bytes.fromhex(mixed["plain_hex"])
    check(plain[:-4] == b"xy" + bytes.fromhex(literal["plain_hex"]), "raw retained and metadata omitted")
    check(plain[-4:] == plain[-5:-4] * 4 and plain[-8:-4] != plain[-4:]
          and mix_commands[-1][5:9] == [2, 0, 4, 0], "distance-one overlap uses prior block's recent ring and bytes")
    legacy, _, _ = accepted("I-only predecessor", work, SWITCHED["assemble"](), reference, traced,
                            [[0, 0, 0, 20], [0, 1, 0, 3], [1, 0, 0, 14]], previous=True)
    return {"libbrotli_commit": PIN, "literal": literal, "mixed": mixed, "predecessor": legacy,
            "failures": failures(work, reference, literal, mixed, mixed_payloads),
            "unsupported": unsupported(work, reference)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-literal-stream-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, SCRIPTS / "brotli-literal-switch/trace-reference.py")
        report = collect(work, reference, traced)
        check(report == json.loads((HERE / "fixtures.json").read_text()), "pinned whole-stream replay")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
