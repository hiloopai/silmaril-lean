#!/usr/bin/env python3
"""Check exact dictionary-aware Brotli streams with pinned libbrotli."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import runpy
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
BLOCK = runpy.run_path(str(SCRIPTS / "brotli-dictionary-block/check.py"))
COMMAND, MAPS, PIN, check, run = (BLOCK[name] for name in ("COMMAND", "MAPS", "PIN", "check", "run"))


def assemble_mixed():
    """Build backward-copy, raw, metadata, dictionary and inherited-copy blocks."""
    switched = runpy.run_path(str(SCRIPTS / "brotli-distance-switch/check.py"))
    bits = switched["SWITCH"]["Bits"]()

    def original(wire):
        return [byte >> bit & 1 for byte in wire for bit in range(8)]

    def compressed_header(length, last):
        bits.code("1000" if last else "000")
        bits.integer(length - 1, 16)
        if not last:
            bits.code("0")

    def aligned_bytes(data):
        bits.code("0" * (-len(bits.bits) % 8))
        for byte in data:
            bits.integer(byte, 8)

    bits.code("0")  # Standard window 16.
    compressed_header(17, False)
    bits.bits.extend(original(switched["assemble"]())[21:199])  # Pinned preceding D-switch payload.
    bits.code("000")  # Non-last raw header, 16-bit MLEN.
    bits.integer(1, 16)
    bits.code("1")
    aligned_bytes(b"xy")
    bits.code("0110")  # Non-last metadata header, reserved bit zero.
    bits.integer(1, 2)
    bits.integer(2, 8)
    aligned_bytes(b"tag")
    compressed_header(7, False)
    bits.bits.extend(original(BLOCK["assemble_empty_then_grow"]())[21:92])
    bits.integer(6148 + 19, 14)  # History has 19 bytes; keep the same word ID.
    bits.code("1")  # Distance type switch after the empty transform.
    bits.integer(0, 2)
    bits.integer(1028 + 19, 14)
    compressed_header(4, True)
    bits.code("000" "000000" "00" "00")  # One L/I/D type each.
    bits.simple(256, [65])
    bits.simple(704, [2])  # Implicit distance, no insertion, copy four; consumes zero payload bits.
    bits.simple(64, [16])
    return bits.pack()


def observe(wire, reference, traced):
    output = run(reference, "-d", "-c", data=wire).stdout
    extent = 8 * len(wire)
    blocks = []
    ring = [4, 11, 15, 16]
    for row in MAPS["native_trace"](wire, reference, traced):
        tag, *values = row.split()
        values = list(map(int, values))
        if tag == "envelope":
            last, metadata, raw, length, unread = values
            kind = "metadata" if metadata else "raw" if raw else "compressed"
            blocks.append({"kind": kind, "last": last, "extent": length, "tables": extent - unread,
                           "beforeRing": ring, "commands": 0, "dictionary": [], "switches": []})
        elif tag == "payload":
            blocks[-1]["payload"] = extent - values[0]
        elif tag == "command":
            blocks[-1]["commands"] += 1
            symbol = values[1]
        elif tag == "switch":
            category, symbol, previous, current, count, start, after_type, stop = values
            blocks[-1]["switches"].append([category, symbol, previous, current, count,
                                           extent - start, extent - after_type, extent - stop])
        elif tag == "distance_end":
            unread, produced, maximum, distance, length = values
        elif tag == "dictionary_emit":
            word_id, ordinal, base, length = values
            check(word_id == distance - maximum - 1 and blocks[-1]["commands"] > 0, "native dictionary address")
            blocks[-1]["dictionary"].append([symbol, base, ordinal, length, produced, extent - unread])
        elif tag in ("back", "dictionary", "terminal_ring"):
            ring = values
        elif tag == "envelope_end":
            blocks[-1].update(end=extent - values[0], afterRing=ring)
    check(blocks[-1]["last"] == 1 and all(block["last"] == 0 for block in blocks[:-1]), "native last flag")
    check(any(block["dictionary"] for block in blocks), "native dictionary dependency")
    check(sum(block["extent"] for block in blocks if block["kind"] != "metadata") == len(output),
          "native exact output extent")
    return output, blocks


def lean(work, wire, output, blocks, commands, bits=None, max_input=None, window=None):
    path = work / "input.br"
    path.write_bytes(wire)
    return json.loads(run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                          "--run", HERE / "Interop.lean", path,
                          str(len(wire) if max_input is None else max_input), str(output),
                          str((1 << 24) - 16 if window is None else window),
                          str(8 * len(wire) if bits is None else bits), str(blocks), str(commands)).stdout)


def compare(work, wire, output, blocks):
    slots = sum(block["commands"] for block in blocks)
    for spare in (0, 1):
        actual = lean(work, wire, len(output), len(blocks), slots + spare)
        expected = {"output": list(output), "ring": blocks[-1]["afterRing"],
                    "remainingCommands": spare, "strictRefused": True}
        check(actual == expected, f"exact bytes, ring, command debit or strict refusal: {str(actual)[:240]}")
    return {"wire_sha256": sha256(wire).hexdigest(), "output_sha256": sha256(output).hexdigest(),
            "output_bytes": len(output), "commands": slots, "blocks": blocks}


def controls(work, wire, output, blocks, reference):
    count = len(blocks)
    commands = sum(block["commands"] for block in blocks)
    end, dictionary = blocks[-1]["end"], blocks[-2]
    check(end < 8 * len(wire) and dictionary["dictionary"][0][3] == 0, "padding and empty command controls")
    changed_pad = bytearray(wire)
    changed_pad[end // 8] ^= 1 << (end % 8)
    check(subprocess.run([reference, "-d", "-c"], input=changed_pad, capture_output=True).returncode != 0,
          "native rejects corrupt final padding")
    size = len(output)
    failures = {}

    def check_error(name, source, block, command, site, cause, bit,
                    output=size, max_blocks=count, slots=commands, **caps):
        expected = {"block": block, "command": command, "stage": site, "cause": cause, "bit": bit}
        found = lean(work, source, output, max_blocks, slots, **caps)
        check(found == {"failure": expected}, f"{name}: {found}")
        failures[name] = expected

    prior = sum(block["commands"] for block in blocks[:-2])
    check_error("dictionary-slot", wire, 3, 0, "fuel", "", dictionary["payload"], slots=prior)
    check_error("zero-output-spends-slot", wire, 3, 1, "fuel", "", dictionary["dictionary"][0][-1], slots=prior + 1)
    check_error("global-slot", wire, 4, 0, "fuel", "", blocks[-1]["payload"], slots=commands - 1)
    late = dictionary["dictionary"][-1][-1]
    at_code = dictionary["switches"][-1][-1]
    truncated = wire[:(late - 1) // 8]
    check(at_code < 8 * len(truncated) < late, "truncate the second dictionary distance")
    check(subprocess.run([reference, "-d", "-c"], input=truncated, capture_output=True).returncode != 0,
          "native rejects a truncated dictionary distance")
    site = "Silmaril.Formats.Compression.Brotli.Distance.Error."
    check_error("late-truncation", truncated, 3, 1, "distance", site + "truncatedExtra", at_code, bits=8 * len(wire))
    check_error("late-bit-cap", wire, 3, 1, "distance", site + "extraBitLimit", at_code, bits=late - 1)
    check_error("block-cap", wire, 4, None, "envelope", "Silmaril.Formats.Compression.Brotli.Error.stepLimit",
                dictionary["end"], max_blocks=count - 1)
    check_error("output-cap", wire, 4, None, "envelope", "Silmaril.Formats.Compression.Brotli.Error.outputLimit",
                blocks[-1]["tables"], output=size - 1)
    check_error("bad-padding", bytes(changed_pad), 4, None, "envelope",
                "Silmaril.Formats.Compression.Brotli.Error.nonzeroPadding", end)
    check_error("trailing-byte", wire + b"\xa5", 4, None, "envelope",
                "Silmaril.Formats.Compression.Brotli.Error.trailingInput", end)
    check_error("padding-budget", wire, 4, None, "envelope", "bitLimit", end, bits=end)
    check_error("window-budget", wire, None, None, "envelope",
                "Silmaril.Formats.Compression.Brotli.Error.windowLimit", 0, window=(1 << 16) - 17)
    check_error("input-budget", wire, None, None, "envelope",
                "Silmaril.Formats.Compression.Brotli.Error.inputLimit", 0, max_input=len(wire) - 1)
    return failures


def collect(work, reference, traced):
    profiles = {}
    for name, quality, plaintext in COMMAND["producer_inputs"]():
        wire = run(reference, "-q", str(quality), "-w", "18", "-c", data=plaintext).stdout
        output, blocks = observe(wire, reference, traced)
        profile = compare(work, wire, output, blocks)
        pins = BLOCK["COMMAND_PINS"][name]
        check(output == plaintext and profile["commands"] == pins["commands"]
              and profile["wire_sha256"] == pins["wire_sha256"], "original native producer pins")
        profiles[name] = profile
        print(f"{name}: {len(output)} exact bytes, {profile['commands']} command slots")
    wire = assemble_mixed()
    output, blocks = observe(wire, reference, traced)
    check([block["kind"] for block in blocks] == ["compressed", "raw", "metadata", "compressed", "compressed"],
          "assembled mixed layout")
    check(output == b"ACACACACCACAACAAAxytiming ng n" and blocks[3]["afterRing"] == blocks[4]["beforeRing"]
          == [3, 5, 2, 4] and output[-4:] != output[-8:-4], "inherited distance materially affects following bytes")
    profile = compare(work, wire, output, blocks)
    profile["wire_hex"] = wire.hex()
    profile["output_hex"] = output.hex()
    profile["failures"] = controls(work, wire, output, blocks, reference)
    print(f"assembled-mixed: {len(blocks)} blocks, {profile['commands']} shared slots, inherited ring {blocks[-1]['afterRing']}")
    print(f"assembled-mixed: {len(profile['failures'])} typed controls with original offsets")
    return {"libbrotli_commit": PIN, "native": profiles, "assembled": profile}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-dictionary-stream-") as directory:
        work = Path(directory)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        traced = MAPS["setup_trace"](source or clean / "brotli", work,
                                     SCRIPTS / "brotli-dictionary-command/trace-reference.py")
        actual = collect(work, reference, traced)
        check(actual == json.loads((HERE / "fixtures.json").read_text()), "pinned dictionary stream replay")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
