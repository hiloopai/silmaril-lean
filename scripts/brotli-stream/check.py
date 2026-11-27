#!/usr/bin/env python3
"""Replay whole streams using pinned libbrotli producers and decoder."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import random
import runpy
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
EXECUTE = runpy.run_path(str(SCRIPTS / "brotli-execute/check.py"))
MAPS = EXECUTE["MAPS"]
PIN, check, run = EXECUTE["PIN"], EXECUTE["check"], EXECUTE["run"]


def lean_decode(work, wire, output=8192, bits=None, blocks=32):
    path = work / "wire.br"
    path.write_bytes(wire)
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", path, str(output),
                 str(8 * len(wire) if bits is None else bits), str(blocks))
    return json.loads(result.stdout)


def flip_bit(data, bit):
    changed = bytearray(data)
    changed[bit // 8] ^= 1 << (bit % 8)
    return bytes(changed)


def mixed_cases(source, reference, work):
    writer = work / "mixed-writer"
    native_build = reference.parent
    run("cc", "-Wall", "-Wextra", "-Werror", "-I", source / "c/include", HERE / "mixed-writer.c",
        "-L", native_build, f"-Wl,-rpath,{native_build}", "-lbrotlienc", "-o", writer)
    rng = random.Random(2316)
    noise = bytes(rng.randrange(256) for _ in range(512))
    for name, first, second, metadata in (
        ("raw-metadata-compressed", noise, noise[128:] * 2, 17),
        ("compressed-metadata-raw", b"ab" * 300, noise, 257),
    ):
        data = first + second
        wire = run(writer, str(len(first)), str(metadata), data=data).stdout
        yield name, data, wire, f"libbrotli streaming encoder quality 9 with {metadata} metadata bytes"


def collect(source, reference, traced, work):
    fixtures = {}
    failures = {}
    cases = list(EXECUTE["input_cases"](source, reference, work))
    cases.extend(mixed_cases(source, reference, work))
    for name, data, wire, producer in cases:
        rows = MAPS["native_trace"](wire, reference, traced)
        check(run(reference, "-d", "-c", data=wire).stdout == data, f"{name}: native original bytes")
        envelope = [[int(x) for x in row.split()[1:]] for row in rows if row.startswith("envelope ")]
        extent = len(wire) * 8
        for row in envelope:
            row[-1] = extent - row[-1]
        ends = [extent - int(row.split()[1]) for row in rows if row.startswith("envelope_end ")]
        actual = lean_decode(work, wire, output=len(data), blocks=len(envelope))
        dictionary = next((row for row in rows if row.startswith("dictionary_id ")), None)
        native_rings = [list(map(int, row.split()[1:])) for row in rows
                        if row.startswith(("back ", "terminal_ring "))]
        if dictionary:
            position = extent - int(next(row.split()[-2] for row in rows if row.startswith("command ")))
            _, _, _, _, distance, length = next(row.split() for row in rows if row.startswith("distance_end "))
            word_id = int(dictionary.split()[1])
            check(actual == {"bit": position, "block": 0, "command": 0,
                             "cause": {"dictionary": [int(distance), int(length), word_id]}},
                  f"{name}: original dictionary cause and coordinates: {actual}")
            failures[name] = actual
        else:
            check(actual == {"output": list(data), "ring": native_rings[-1]}, f"{name}: bytes and final ring")
            if name in {"flushed-cross-metablock", "raw-metadata-compressed", "compressed-metadata-raw"}:
                controls = {
                    "trailing": (wire + b"\0", len(data), 8 * len(wire) + 8, len(envelope)),
                    "short-bit-cap": (wire, len(data), extent - 1, len(envelope)),
                    "short-output-cap": (wire, len(data) - 1, extent, len(envelope)),
                    "short-block-cap": (wire, len(data), extent, len(envelope) - 1),
                    "truncated-last-byte": (wire[:-1], len(data), extent, len(envelope)),
                }
                check(ends[-1] < extent, f"{name}: native final zero fill")
                controls["nonzero-final-fill"] = (flip_bit(wire, ends[-1]), len(data), extent, len(envelope))
                last_block = len(envelope) - 1
                last_data = max(i for i, row in enumerate(envelope) if row[1] == 0 and row[3] > 0)
                late_command = next((row for row in rows if row.startswith("command ") and
                                     extent - int(row.split()[-2]) >= ends[-2]), None)
                truncated = ((last_block, extent - int(late_command.split()[-2]), 0, "truncatedExtra")
                             if late_command else (last_block, ends[-2], None, "truncated"))
                expected = {
                    "trailing": (last_block, ends[-1], None, "trailingInput"),
                    "short-bit-cap": (last_block, ends[-1], None, "bitLimit"),
                    "short-output-cap": (last_data, envelope[last_data][-1], None, "outputLimit"),
                    "short-block-cap": (last_block, ends[-2], None, "stepLimit"),
                    "truncated-last-byte": truncated,
                    "nonzero-final-fill": (last_block, ends[-1], None, "nonzeroPadding"),
                }
                if late_command:
                    check(envelope[-1][:4] == [1, 0, 0, 768], "late compressed MLEN")
                    controls["short-mlen"] = (flip_bit(wire, ends[-2] + 4), len(data), extent, len(envelope))
                    expected["short-mlen"] = (
                        last_block, extent - int(late_command.split()[-2]), 0, "metaBlockExtent")
                for kind, args in controls.items():
                    rejected = lean_decode(work, *args)
                    block, bit, command, cause = expected[kind]
                    check((rejected.get("block"), rejected.get("bit"), rejected.get("command")) ==
                          (block, bit, command) and rejected["cause"].rstrip(")").endswith(cause),
                          f"{name}: late {kind} rejection: {rejected}")
                    failures[f"{name}/{kind}"] = rejected
        crossing = []
        for row in rows:
            if row.startswith("distance_end "):
                _, _, produced, _, distance, length = row.split()
                position, distance, length = map(int, (produced, distance, length))
                if position >= 512 and position - distance < 512:
                    crossing.append([position, distance, length])
        if name in {"flushed-cross-metablock", "raw-metadata-compressed"}:
            check([512, 384, 768] in crossing, f"{name}: native copy takes earlier block bytes")
        fixtures[name] = {"producer": producer, "wire_sha256": sha256(wire).hexdigest(),
                          "output_sha256": sha256(data).hexdigest(), "output_size": len(data),
                          "blocks": envelope, "block_end_bits": ends, "ring": actual.get("ring")}
        print(f"{name}: {len(data)} native output bytes; meta-block headers {envelope}; "
              f"{'typed dictionary rejection' if dictionary else 'matched bytes and final ring'}")
    check([row[1:4] for row in fixtures["raw-metadata-compressed"]["blocks"]]
          == [[0, 1, 512], [1, 0, 17], [0, 0, 768]], "native raw/metadata/compressed order")
    check([row[1:4] for row in fixtures["compressed-metadata-raw"]["blocks"] if row[3]]
          == [[0, 0, 600], [1, 0, 257], [0, 1, 512]], "native compressed/metadata/raw order")
    failures["switching"] = switching_control(reference, traced, work)
    return {"libbrotli_commit": PIN, "fixtures": fixtures, "failures": failures}


def switching_control(reference, traced, work):
    rng = random.Random(281)
    plain = b"".join(bytes(65 + 20 * (j % 3) + rng.randrange(j % 3 + 2)
                           for _ in range(8192)) for j in range(6))
    wire = run(reference, "-q", "11", "-w", "18", "-c", data=plain).stdout
    rows = MAPS["native_trace"](wire, reference, traced)
    types = [int(row.split()[2]) for row in rows if row.startswith("types ")][:3]
    check(max(types) > 1, "native switching control")
    header = next(row.split() for row in rows if row.startswith("envelope "))
    actual = lean_decode(work, wire, output=len(plain))
    check(actual == {"bit": 8 * len(wire) - int(header[-1]), "block": 0, "command": None,
                     "cause": "unsupported block switching"}, f"switching coordinates and cause: {actual}")
    print(f"switching: rejected native block types {types} at bit {actual['bit']}")
    return {"wire_sha256": sha256(wire).hexdigest(), "types": types, **actual}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-stream-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        report = collect(source, reference, traced, work)
        check(report == json.loads((HERE / "fixtures.json").read_text()), "pinned wire/output and failure receipts")
        print(f"Fixture manifest matched libbrotli {PIN}; {len(report['failures'])} typed controls")


if __name__ == "__main__":
    main()
