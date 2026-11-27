#!/usr/bin/env python3
"""Execute producer streams from original bytes and compare bytes and cursors."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import random
import runpy
from tempfile import TemporaryDirectory

import pyarrow as pa

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
MAPS = runpy.run_path(str(SCRIPTS / "brotli-context-maps/check.py"))
LITERALS = runpy.run_path(str(SCRIPTS / "brotli-literal/check.py"))
PIN, check, run = MAPS["PIN"], MAPS["check"], MAPS["run"]


def input_cases(source, reference, work):
    for name, data in (
        ("cli-distance-one", b"a" * 1024),
        ("cli-distance-two", b"ab" * 700),
        ("cli-literal-only", LITERALS["debruijn_pairs"](b"abcdefghijklmnop")),
    ):
        wire = run(reference, "-q", "4", "-w", "18", "-c", data=data).stdout
        yield name, data, wire, "libbrotli CLI quality 4"

    writer = work / "flush-writer"
    native_build = reference.parent
    run("cc", "-Wall", "-Wextra", "-Werror", "-I", source / "c/include", HERE / "flush-writer.c",
        "-L", native_build, f"-Wl,-rpath,{native_build}", "-lbrotlienc", "-o", writer)
    rng = random.Random(281)
    first = bytes(rng.randrange(200, 216) for _ in range(512))
    data = first + first[128:] * 2
    wire = run(writer, "512", "9", data=data).stdout
    yield "flushed-cross-metablock", data, wire, "libbrotli streaming encoder quality 9"

    data = b"".join(
        f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
        for i in range(99))
    wire = run(reference, "-q", "7", "-w", "18", "-c", data=data).stdout
    yield "cli-dictionary", data, wire, "libbrotli CLI quality 7"


def observe(wire, data, reference, traced):
    rows = MAPS["native_trace"](wire, reference, traced)
    check(run(reference, "-d", "-c", data=wire).stdout == data, "native original bytes")
    extent = 8 * len(wire)
    produced = 0
    commands = []
    cross = []
    for row in rows:
        label, *words = row.split()
        values = list(map(int, words))
        if label == "types":
            check(values[1] == 1, "one native block type")
        elif label == "metablock":
            block_start, length = produced, values[0]
        elif label == "command":
            _, _, insert, copy, _mode, before, _after = values
            command_start = extent - before
        elif label == "terminal_command":
            remaining, final = values
            stop = extent - remaining
            distance = 0
        elif label == "distance_end":
            remaining, position, _, distance, word_length = values
            check(position == produced + insert and copy == word_length, "native produced counts")
            stop = extent - remaining
            final = position + copy
        elif label == "dictionary_id":
            return data[:produced], commands, [command_start, distance, word_length, values[0]], cross
        elif label in ("back", "terminal_ring"):
            commands.append([block_start, length, command_start, stop, final, insert, copy, distance, *values])
            if distance and produced + insert - distance < block_start:
                cross.append([produced + insert, distance, copy])
            produced = final
    check(produced == len(data), "native command output extent")
    return data, commands, None, cross


def collect(source, reference, traced, work):
    fixtures = {}
    for name, data, wire, provenance in input_cases(source, reference, work):
        plain, commands, dictionary, cross = observe(wire, data, reference, traced)
        path = work / "wire.br"
        path.write_bytes(wire)
        result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                     "--run", HERE / "Interop.lean", path)
        actual = json.loads(result.stdout)
        check(actual["output"] == list(plain), f"{name}: Lean output bytes")
        check(actual["commands"] == commands, f"{name}: Lean cursor, distance, output count or ring")
        check(actual["dictionary"] == dictionary, f"{name}: Lean dictionary handoff")
        distances = [row[7] for row in commands if row[7]]
        trace = json.dumps(commands, separators=(",", ":")).encode()
        fixtures[name] = {"provenance": provenance, "wire_sha256": sha256(wire).hexdigest(),
                          "output_sha256": sha256(plain).hexdigest(), "trace_sha256": sha256(trace).hexdigest(),
                          "bytes": len(plain), "commands": len(commands), "distances": distances,
                          "cross_metablock": cross, "dictionary": dictionary}
        print(f"{name}: {len(plain)} bytes, {len(commands)} accepted commands, distances={distances}, "
              f"cross-meta-block={cross}, dictionary={dictionary}")
    check(fixtures["cli-distance-one"]["distances"] == [1] and
          fixtures["cli-distance-two"]["distances"] == [2], "small overlapping distances")
    check(fixtures["flushed-cross-metablock"]["cross_metablock"], "cross-meta-block copy")
    check(fixtures["cli-dictionary"]["dictionary"], "unsupported dictionary branch")
    return {"libbrotli_commit": PIN, "fixtures": fixtures}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "harness versions")
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-execute-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        manifest = collect(source, reference, traced, work)
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "execution pins")
        print(f"Fixture manifest matched libbrotli {PIN}")


if __name__ == "__main__":
    main()
