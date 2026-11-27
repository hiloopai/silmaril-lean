#!/usr/bin/env python3
"""Compare the distance-switching payload entry point with pinned libbrotli."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import runpy
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
COMMAND = runpy.run_path(str(SCRIPTS / "brotli-distance-switch/check.py"))
PIN, check, run, MAPS = COMMAND["PIN"], COMMAND["check"], COMMAND["run"], COMMAND["MAPS"]


def assemble_pair(wire, payload, end):
    """Reframe the checked D specimen twice and start the second with an implicit copy."""
    bits = COMMAND["SWITCH"]["Bits"]()
    original = [byte >> index & 1 for byte in wire for index in range(8)]
    check(original[:5] == [0, 1, 0, 0, 0], "original window and final compressed framing")
    bits.code("0000")  # Same standard window, non-last, length selector zero.
    bits.integer(16, 16)
    bits.code("0")  # Non-last compressed body.
    bits.bits.extend(original[21:end])
    bits.code("1000")  # Last, nonempty, length selector zero.
    bits.integer(20, 16)  # Second MLEN 21.
    bits.bits.extend(original[21:payload])
    bits.code("00")  # Previously declared command code 2, implicit distance.
    bits.bits.extend(original[payload:end])
    return bits.pack()


def observe(wire, reference, traced):
    plain = run(reference, "-d", "-c", data=wire).stdout
    extent = 8 * len(wire)
    rows = MAPS["native_trace"](wire, reference, traced)
    blocks, commands, switches = [], [], []
    start = 0
    for row in rows:
        label, *values = row.split()
        values = list(map(int, values))
        if label == "envelope":
            last, metadata, raw, length, unread = values
            check(not metadata and not raw, "independent fixture has only compressed meta-blocks")
            header = extent - unread
            index = len(blocks)
            count = 0
        elif label == "payload":
            payload = extent - values[0]
        elif label == "command":
            count += 1
        elif label == "switch":
            category, symbol, previous, current, run_length, before, after_type, after = values
            check(category == 2, "native D switch")
            switches.append([index, count - 1, symbol, previous, current, run_length,
                             extent - before, extent - after_type, extent - after])
        elif label == "distance_run":
            active = values
        elif label == "distance_end":
            unread, produced, maximum, distance, copied = values
            check(distance <= maximum, "independent fixture only uses backward references")
            commands.append([index, count - 1, distance, produced, copied, extent - unread, *active])
        elif label in ("back", "terminal_ring"):
            ring = values
        elif label == "envelope_end":
            end = extent - values[0]
            blocks.append({"bytes": list(plain[start:start + length]), "header": header, "payload": payload,
                           "end": end, "ring": ring, "distanceRun": active})
            start += length
    check(start == len(plain) and last == 1, "exact native full output")
    return plain, blocks, commands, switches


def lean_decode(work, wire, output, bits):
    path = work / "wire.br"
    path.write_bytes(wire)
    reply = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                HERE / "Interop.lean", path, str(output), str(bits))
    return json.loads(reply.stdout)


def accepted(name, work, wire, reference, traced, sizes, switch_count):
    plain, blocks, commands, switches = observe(wire, reference, traced)
    check([len(row["bytes"]) for row in blocks] == sizes and len(switches) == switch_count,
          f"{name}: native block and switch counts")
    actual = lean_decode(work, wire, len(plain), 8 * len(wire))
    check(actual == {"blocks": blocks, "finish": "ok"}, f"{name}: actual payload reader {actual}")
    print(f"{name}: {len(plain)} bytes, {len(blocks)} blocks, {len(switches)} switches")
    return {"sha256": sha256(wire).hexdigest(), "wire_hex": wire.hex(), "plain_hex": plain.hex(),
            "blocks": blocks, "copies": commands, "switches": switches}


def collect(work, reference, traced):
    wire = COMMAND["assemble"]()
    single = accepted("D specimen", work, wire, reference, traced, [17], 2)
    first = single["blocks"][0]
    wire = assemble_pair(wire, first["payload"], first["end"])
    pair = accepted("D pair with inherited copy", work, wire, reference, traced, [17, 21], 4)
    plain = bytes.fromhex(pair["plain_hex"])
    blocks, copies, switches = pair["blocks"], pair["copies"], pair["switches"]
    check(copies[4][:5] == [1, 0, 3, 17, 4] and copies[4][-3:] == [0, 1, 1],
          "second block starts with fresh D run and inherited distance 3")
    check(plain[17:21] == b"AAAA" and plain[13:17] != plain[17:21],
          "the inherited distance and history produce different bytes from a reset ring")
    check(lean_decode(work, wire + b"\xa5", len(plain), 8 * (len(wire) + 1)) ==
          {"blocks": blocks, "finish": "trailingInput"}, "block reader preserves the final trailer")
    extent = 8 * len(wire)
    truncated = wire[:-1]
    check(subprocess.run([reference, "-d", "-c"], input=truncated, capture_output=True).returncode != 0,
          "native byte truncation")
    late = switches[2]
    regular_end = next(row[5] for row in copies if row[:2] == late[:2])
    cases = (
        ("late-type-cap", wire, len(plain), late[-3], "switch-type", late[1], late[-3], "bitLimit"),
        ("late-count-cap", wire, len(plain), late[-2] + 1, "switch-length", late[1], late[-2], "bitLimit"),
        ("late-symbol-cap", wire, len(plain), late[-1], "distance", late[1], late[-1], "bitLimit"),
        ("late-output-cap", wire, 32, extent, "copy", late[1], regular_end, "outputLimit"),
        ("late-truncation", truncated, len(plain), extent, "switch-type", switches[-1][1],
         switches[-1][-3], "truncated"),
    )
    failures = {}
    for name, source, output, bits, kind, command, bit, cause in cases:
        actual = lean_decode(work, source, output, bits)["failure"]
        check((actual["block"], actual["stage"], actual["command"], actual["bit"]) == (1, kind, command, bit)
              and actual["cause"].rstrip(")").endswith("." + cause), f"{name}: {actual}")
        failures[name] = actual
        print(f"{name}: {kind} at original bit {bit}, block 1, command {command}")

    dictionary_plain = b"".join(f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
                                for i in range(99))
    dictionary = run(reference, "-q", "7", "-w", "18", "-c", data=dictionary_plain).stdout
    prior = json.loads((SCRIPTS / "brotli-distance-switch/fixtures.json").read_text())["native_dictionary"]
    check(sha256(dictionary).hexdigest() == prior["sha256"], "pinned native dictionary control")
    check(run(reference, "-d", "-c", data=dictionary).stdout == dictionary_plain, "native dictionary output")
    failed = lean_decode(work, dictionary, len(dictionary_plain), 8 * len(dictionary))["failure"]
    check(failed == dict(prior["failure"], block=0), f"unchanged indexed typed dictionary refusal {failed}")
    print(f"Native dictionary rejected at original bit {failed['bit']}, block 0, command 0")
    return {"libbrotli_commit": PIN, "single": single, "pair": pair, "trailer": "a5",
            "failures": failures, "native_dictionary": {"sha256": prior["sha256"], "failure": failed}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-distance-block-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, SCRIPTS / "brotli-distance-switch/trace-reference.py")
        report = collect(work, reference, traced)
        check(report == json.loads((HERE / "fixtures.json").read_text()), "pinned distance block replay")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
