#!/usr/bin/env python3
"""Compare resolved Brotli distances and recent rings against libbrotli."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import runpy
from tempfile import TemporaryDirectory

import pyarrow as pa

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
MAPS = runpy.run_path(str(SCRIPTS / "brotli-context-maps/check.py"))
PIN, check, run = MAPS["PIN"], MAPS["check"], MAPS["run"]


def parse(wire, rows):
    extent = 8 * len(wire)
    start = extent - int(next(row.split()[-1] for row in rows if row.startswith("start 0 ")))
    types = int(next(row.split()[2] for row in rows if row.startswith("types 2 ")))
    if types != 1:
        return None
    payloads = [extent - int(row.split()[1]) for row in rows if row.startswith("payload ")]
    check(len(payloads) == 1, "native compressed meta-block count")
    requests, expected = [], []
    command = None
    for row in rows:
        label, *words = row.split()
        values = list(map(int, words))
        if label == "command":
            command = values
        elif label == "distance_begin":
            remaining, explicit, context = values
            begin = extent - remaining
            code, extra, selection, target = 0, 0, [], []
        elif label == "ring_before":
            ring = values
        elif label == "distance_code":
            code, extra, tree = values
            selection = [context, tree]
        elif label == "distance_end":
            remaining, produced, maximum, distance, length = values
            end = extent - remaining
            check(bool(selection) == bool(explicit) and command is not None, "native distance mode")
            command_type, symbol, _, copy_length, mode, command_begin, command_end = command
            check((copy_length, mode) == (length, explicit) and extent - command_end <= begin,
                  "native command and distance join")
            target = [distance]
        elif label == "dictionary_id":
            target.extend((length, values[0]))
        elif label in ("back", "dictionary"):
            check(bool(len(target) == 3) == (label == "dictionary"), "native classification")
            requests.append([command_type, extent - command_begin, begin, end, produced])
            expected.append([[symbol, copy_length, maximum, code, extra, begin, end],
                             selection, target, ring, values])
    check(expected and requests[0][1] == payloads[0], "native first distance")
    check(len(expected) == sum(row.startswith("distance_end ") for row in rows), "native distance outcomes")
    return start, payloads[0], requests, expected


def collect(source, reference, traced, harness, work):
    header = MAPS["HEADER"]
    writer = work / "parameter-writer"
    native_build = reference.parent
    run("cc", "-Wall", "-Wextra", "-Werror", "-I", source / "c/include",
        SCRIPTS / "brotli-context-header/parameter-writer.c", "-L", native_build,
        f"-Wl,-rpath,{native_build}", "-lbrotlienc", "-o", writer)
    output = {}
    for name, (wire, provenance, params) in header["inputs"](reference, writer, harness, work).items():
        if name == "cli-utf8-multiple":
            # Its distance section uses two block types.
            continue
        observed = parse(wire, MAPS["native_trace"](wire, reference, traced))
        check(observed is not None, "one native distance block type")
        start, payload, requests, expected = observed
        source_file = work / "wire.br"
        source_file.write_bytes(wire)
        trace_file = work / "requests"
        trace_file.write_text("".join(" ".join(map(str, row)) + "\n" for row in requests))
        result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                     "--run", HERE / "Interop.lean", source_file, trace_file, str(start), str(payload))
        check([json.loads(row) for row in result.stdout.splitlines()] == expected,
              f"{name}: native distances, selected trees or rings")
        implicit = sum(not row[1] for row in expected)
        dictionary = sum(len(row[2]) == 3 for row in expected)
        postfix, ndirect = params or (0, 0)
        direct = sum(16 <= row[0][3] < 16 + ndirect for row in expected)
        short = sum(bool(row[1]) and row[0][3] < 16 for row in expected)
        regular = sum(row[0][3] >= 16 + ndirect for row in expected)
        trees = sorted({row[1][1] for row in expected if row[1]})
        output[name] = {"provenance": provenance, "wire_sha256": sha256(wire).hexdigest(),
                        "trace_sha256": sha256(json.dumps(expected, separators=(",", ":")).encode()).hexdigest(),
                        "start": start, "payload": payload, "copies": len(expected), "implicit": implicit,
                        "dictionary": dictionary, "short": short, "direct": direct, "regular": regular,
                        "postfix": postfix, "ndirect": ndirect, "trees": trees}
        print(f"{name}: {len(expected)} distances, {implicit} implicit, {dictionary} dictionary, "
              f"{direct} direct, trees {trees}")
    check(any(row["dictionary"] for row in output.values()), "dictionary fixtures")
    check(any(row["direct"] for row in output.values()), "direct code fixtures")
    check({row["postfix"] for row in output.values() if row["regular"]} == {0, 1, 2, 3},
          "regular distances at each postfix width")
    check(any(len(row["trees"]) > 1 for row in output.values()), "context-selected trees")
    return {"libbrotli_commit": PIN, "fixtures": output}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-distance-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        manifest = collect(source, reference, traced, harness, work)
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "distance and ring pins")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
