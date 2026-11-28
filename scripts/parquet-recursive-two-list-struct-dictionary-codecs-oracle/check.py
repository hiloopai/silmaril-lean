"""Inspect original compressed TwoListStruct dictionaries and page-local values."""

from collections import Counter
from copy import deepcopy
from dataclasses import dataclass
import json
from pathlib import Path
import runpy
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
PREVIOUS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-dictionary-oracle/check.py"))
REFERENCE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-more-codecs-oracle/check.py"))
LIST_PATH = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-dictionary-codecs-oracle/check.py"))
BASE, NATIVE, SNAPPY, IPC, THRIFT, LEAN = (PREVIOUS[key] for key in
                                        ("BASE", "NATIVE", "SNAPPY", "IPC", "THRIFT", "LEAN"))
encode, frames, header_body, raw_chunks, repack = (PREVIOUS[key] for key in
                                                  ("encode", "frames", "header_body", "raw_chunks", "repack"))
PRODUCERS, payload_parts, ZSTD_FRAME = (LIST_PATH[key] for key in ("PRODUCERS", "payload_parts", "ZSTD_FRAME"))
ALL = (True,) * 4
LATE = (1, 1)


@dataclass(frozen=True)
class Refusal:
    label: str
    reference: str
    ordinal: int
    kind: str
    cause: str
    key: tuple = LATE
    limits: str = "{}"
    check_prefix: bool = True


def native(optional, version, compression, **options):
    flags = ALL if optional else (False, False, False, True)
    schema, groups, _ = SNAPPY["native"](flags, optional, version, reverse=not optional)
    groups = deepcopy(groups)
    groups[1][0][0][-64:] = [{"lo": -17 - i % 2, "hi": (2**40) << (i % 2)} for i in range(192)]
    groups[1].extend([[[{"lo": 100 + i * 4 + j, "hi": 2**45 + i * 4 + j} for j in range(4)]] for i in range(6)])
    settings = dict(compression=compression, data_page_version=f"{version}.0", use_dictionary=True,
                    dictionary_pagesize_limit=64, data_page_size=64, max_rows_per_page=1,
                    write_batch_size=1, write_page_checksum=optional)
    return schema, groups, NATIVE["write"](schema, groups, **(settings | options))


def fixtures(lz4, zstd, decode):
    genuine, authored, positives, refusals = {}, {}, {}, []
    zstd_reference = REFERENCE["ZSTD"]
    zstd_run = zstd_reference["ZSTD"]["run"]

    for name, (codec, producer) in PRODUCERS.items():
        for version in (1, 2):
            for optional, shape in ((True, "optional"), (False, "required")):
                label = f"{name}_v{version}_{shape}"
                case = genuine[label] = positives[label] = native(optional, version, producer)
                assert {meta[4][1] for _, meta, _, _ in NATIVE["V2"]["columns"](case[2])} == {codec}

    path = ".".join(NATIVE["PATH"])
    mixed_codecs = {f"{path}.lo": "ZSTD", f"{path}.hi": "GZIP"}
    label = "native_independent_encodings"
    genuine[label] = positives[label] = native(True, 2, mixed_codecs, use_dictionary=[f"{path}.lo"])
    assert [(meta[4][1], 11 in meta) for _, meta, _, _ in NATIVE["V2"]["columns"](genuine[label][2])] == [
        (6, True), (2, False), (6, True), (2, False)]

    _, previous, cases, _, old_refusals, _ = PREVIOUS["fixtures"]()
    schema, groups, identity = cases["mixed_versions_fallback"]
    authored["uncompressed_reference"] = identity
    positives["uncompressed_reference"] = schema, groups, identity

    def reframe(wire):
        chunks = raw_chunks(wire)
        footer = NATIVE["metadata"](wire)
        codecs = {(0, 0): 7, (0, 1): 1, (1, 0): 2, (1, 1): 6}
        compressors = {
            7: lambda data: pa.Codec("lz4_raw").compress(data).to_pybytes(),
            1: lambda data: pa.Codec("snappy").compress(data).to_pybytes(),
            2: lambda data: zlib.compress(data, wbits=31),
            6: lambda data: zstd_run(zstd, "compress-checksum", data=data),
        }
        for key, pages in chunks.items():
            codec = codecs[key]
            THRIFT["column_metadata"](footer, *key)[4] = TType.I32, codec
            for ordinal, page in enumerate(pages):
                header, body = header_body(page)
                levels, values, size, flagged = payload_parts(header, body)
                assert size == len(values)
                if flagged:
                    pages[ordinal] = encode(header, levels + compressors[codec](values), len(body))
        return repack(wire, chunks, footer)

    mixed = authored["mixed_child_cuts"] = reframe(identity)
    positives["mixed_child_cuts"] = schema, groups, mixed
    former = {label: (ordinal, cause) for label, ordinal, _, cause in old_refusals}
    for version in (1, 2):
        label = f"late_out_of_bounds_v{version}"
        authored[label] = reframe(previous[label])
        ordinal, cause = former[label]
        refusals.append(Refusal(label, "mixed_child_cuts", ordinal, "page", cause))

    def patch(label, source, ordinal, edit, key=LATE):
        wire = positives[source][2]
        chunks = raw_chunks(wire)
        chunks[key][ordinal] = edit(*header_body(chunks[key][ordinal]))
        authored[label] = repack(wire, chunks)

    for name, (codec, _) in PRODUCERS.items():
        source = f"{name}_v2_optional"
        schema, groups, wire = positives[source]
        ordinal = next(i for i, (_, header, _, body) in enumerate(frames(wire, LATE))
                       if header[1][1] == 3 and PREVIOUS["encoding"](header) == 8
                       and payload_parts(header, body)[3] and payload_parts(header, body)[2] >= 8)
        label = f"{name}_raw_index_bypass"
        patch(label, source, ordinal,
              lambda header, body: SNAPPY["raw_bypass"](header, body, decode=lambda b, n: decode(codec, b, n)))
        positives[label] = schema, groups, authored[label]
        _, header, _, stored = frames(authored[label], LATE)[ordinal]
        assert not payload_parts(header, stored)[3]
        assert raw_chunks(authored[label])[LATE][0] == raw_chunks(wire)[LATE][0]

        label = f"late_{name}_dictionary_crc"
        patch(label, source, 0, lambda header, body: encode(header, b"\x80", header[2][1], crc=False))
        _, header, _, stored = frames(authored[label], LATE)[0]
        checksum = f".checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(stored)})"
        refusals.append(Refusal(label, source, 0, "dictionary", checksum))

    def dictionary_edit(label, source, edit, cause):
        patch(label, source, 0, lambda header, body: encode(header, edit(body, header[2][1]), header[2][1]))
        refusals.append(Refusal(label, source, 0, "dictionary", cause))

    def lz4_frame(block, size):
        framed = pa.Codec("lz4_frame").compress(decode(7, block, size)).to_pybytes()
        assert framed.startswith(b"\x04\x22\x4d\x18")
        assert REFERENCE["LZ4"]["reference_decode"](lz4, framed, size) is None
        return framed

    source = "lz4_v1_optional"
    dictionary_edit("late_lz4_framed_dictionary", source, lz4_frame, ".payload .outputSizeMismatch")
    patch("late_lz4_declared_extent", source, 0, lambda header, block: encode(header, block, header[2][1] + 1))
    refusals.append(Refusal("late_lz4_declared_extent", source, 0, "dictionary", ".payload .outputSizeMismatch"))
    wire = genuine[source][2]
    footer = NATIVE["metadata"](wire)
    THRIFT["column_metadata"](footer, *LATE)[4] = TType.I32, 5
    authored["late_legacy_lz4"] = NATIVE["TWO"]["SCHEMA"]["pack"](wire, footer)
    refusals.append(Refusal("late_legacy_lz4", source, 0, "binding", ".codec 5"))

    def gzip_second_member(block, size):
        member = zlib.compress(b"", wbits=31)
        assert REFERENCE["GZIP"]["first_member"](block + member, size)[1] == member
        return block + member

    source = "gzip_v2_optional"
    dictionary_edit("late_gzip_second_member", source, gzip_second_member, ".payload (.trailingInput .gzip)")
    wire = genuine[source][2]
    footer = NATIVE["metadata"](wire)
    meta = THRIFT["column_metadata"](footer, *LATE)
    first = meta[9][1]
    meta[9] = TType.I64, first + 1
    authored["late_data_anchor"] = NATIVE["TWO"]["SCHEMA"]["pack"](wire, footer)
    refusals.append(Refusal("late_data_anchor", source, 1, "dictionary", f".dataOffset {first + 1} {first}"))

    def zstd_id(block, _):
        tag = block[4]
        assert tag & 3 == 0
        at = 5 if tag & 32 else 6
        changed = block[:4] + bytes([tag | 1]) + block[5:at] + b"\x07" + block[at:]
        assert zstd_reference["frame_info"](zstd, changed)[4] == 7
        return changed

    source = "zstd_v2_optional"
    dictionary_edit("late_zstd_dictionary_id", source, zstd_id, ZSTD_FRAME.format("(.unsupportedDictionary 7)"))
    dictionary_edit("late_zstd_second_frame", source, lambda block, _: block + block, ZSTD_FRAME.format(".trailingInput"))
    refusals.append(Refusal(source, source, 0, "dictionary", ZSTD_FRAME.format(".windowLimit"),
                            key=(1, 0), limits=REFERENCE["ZSTD_ZERO"], check_prefix=False))

    # Original producer fixture for an excluded codec at dictionary admission.
    label = "brotli_dictionary"
    genuine[label] = native(True, 2, "BROTLI")
    assert SNAPPY["column_codec"](genuine[label][2], (0, 0)) == 4
    refusals.append(Refusal(label, source, 0, "binding", ".codec 4", key=(0, 0)))
    return genuine, authored, positives, refusals


def verify(folder):
    lz4, zstd, decode = REFERENCE["reference_codecs"](folder)
    genuine, authored, positives, refusals = fixtures(lz4, zstd, decode)
    originals = {label: case[2] for label, case in genuine.items()}
    files = originals | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code, entry, observations, counts = [LEAN], [], {}, Counter()
    for label, (schema, groups, wire) in positives.items():
        tables = {}
        commands, logical, columns, frame_counts = SNAPPY["source_commands"](
            label, schema, groups, wire, decode, checksums=not label.endswith("_required"), dictionaries=tables)
        observations[label] = schema, logical, columns
        counts.update(frame_counts)
        local = Counter()
        extra = PREVIOUS["dictionary_commands"](label, schema, wire, columns, tables, local, decode)
        if label.endswith(("_required", "_optional")):
            assert local["fallback"] > 0 and len(tables) == 4
        if label.endswith("_raw_index_bypass"):
            assert local["raw_index_pages"] > 0
        if label == "mixed_child_cuts":
            assert [page[-1][0][0] for page in columns[1, 0][1][:3]] == [0, 2, 1]
            assert [page[-1][0][0] for page in columns[1, 1][1][:2]] == [0, 2]
        counts.update(local)
        code.extend([f"set_option maxHeartbeats 2000000 in\nprivate def verify_{label} (folder : System.FilePath) : IO Unit := do",
                     *commands, *extra])
        entry.append(f"  verify_{label} folder")

    code.append("private def controls (folder : System.FilePath) : IO Unit := do")
    for control in refusals:
        group = control.key[0]
        address = NATIVE["address"](*control.key)
        schema, logical, columns = observations[control.reference]
        if control.kind == "binding":
            error = f".binding (.column {address} ({control.cause}))"
        else:
            byte = frames(files[control.label], control.key)[control.ordinal][0]
            if control.kind == "dictionary":
                error = f".chunk (.dictionary {address} {control.ordinal} {byte} ({control.cause}))"
            else:
                cursor = SNAPPY["triple"](columns[control.key][1][control.ordinal - 1][-3])
                error = f".chunk (.page {address} {control.ordinal} {byte} {cursor} ({control.cause}))"
        code.append(f'  groupRefusal (← load folder "{control.label}") {group} {control.limits} ({error})')
        if control.check_prefix:
            prefix = IPC["batches_term"](schema, logical[:group])
            code.append(f'  checkFailure (← load folder "{control.label}") {control.limits} {prefix} (.group {group} ({error}))')
    code.extend(['public def main (args : List String) : IO Unit := do',
                 '  let [folder] := args | throw (IO.userError "expected fixture directory")',
                 *entry, "  controls folder"])
    NATIVE["V2"]["run_lean"](folder, "TwoListStructDictionaryCodecs.lean", code)

    ipc = {}
    for label, (schema, logical, _) in observations.items():
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            output = ipc[f"{label}_{selection}"] = (folder / f"{label}_{selection}.arrow").read_bytes()
            IPC["inspect_ipc"](output, projected, logical)
    for selection in ("field", "empty"):
        assert ipc[f"mixed_child_cuts_{selection}"] == ipc[f"uncompressed_reference_{selection}"]
        assert ipc[f"native_independent_encodings_{selection}"] == ipc[f"zstd_v2_optional_{selection}"]
        for name in PRODUCERS:
            assert ipc[f"{name}_raw_index_bypass_{selection}"] == ipc[f"{name}_v2_optional_{selection}"]
    print(f"Checked {len(positives)} carriers, {counts['dictionaries']} original dictionaries, "
          f"{counts['v1']} V1 and {counts['v2']} V2 data pages, {counts['fallback']} PLAIN fallback pages, "
          f"{counts['raw_index_pages']} raw V2 index suffixes, {len(ipc)} exact IPC streams and {len(refusals)} typed controls")
    pins = NATIVE["fingerprints"]
    return {
        "reference": {"liblz4": REFERENCE["LZ4"]["PIN"], "libzstd": REFERENCE["ZSTD"]["ZSTD"]["PIN"],
                      "zlib": zlib.ZLIB_RUNTIME_VERSION},
        "genuine_parquet": pins(originals),
        "authored_parquet": pins(authored),
        "lean_ipc": pins(ipc),
    }


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert BASE["producer"]() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {key: data for key, data in pins.items() if key != "producer"}


if __name__ == "__main__":
    main()
