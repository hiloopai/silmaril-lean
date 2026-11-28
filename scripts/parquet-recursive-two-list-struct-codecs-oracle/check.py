"""Inspect original TwoListStruct LZ4_RAW, GZIP and Zstandard carriers."""

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
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-snappy-oracle/check.py"))
REFERENCE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-more-codecs-oracle/check.py"))
BASE, NATIVE, IPC, THRIFT, LEAN, native = (SNAPPY[key] for key in ("BASE", "NATIVE", "IPC", "THRIFT", "LEAN", "native"))
encode, header_body, raw_chunks, raw_bypass, repack = (SNAPPY[key] for key in
                                                       ("encode", "header_body", "raw_chunks", "raw_bypass", "repack"))
PRODUCERS, parts, GZIP_ZERO, ZSTD_ZERO, ZSTD_FRAME = (REFERENCE[key] for key in
                                                    ("PRODUCERS", "parts", "GZIP_ZERO", "ZSTD_ZERO", "ZSTD_FRAME"))
LATE = (1, 1)
ALL = (True,) * 4


@dataclass(frozen=True)
class Refusal:
    label: str
    original: str
    ordinal: int
    cause: str
    key: tuple = LATE
    caps: str = "{}"
    verify_prefix: bool = True


def set_codec(footer, key, codec):
    THRIFT["column_metadata"](footer, *key)[4] = TType.I32, codec


def frames(wire, key):
    return SNAPPY["frames_in"](wire, *key)


def gzip_bad_crc(member, extent):
    bad = member[:-8] + bytes([member[-8] ^ 1]) + member[-7:]
    try:
        REFERENCE["GZIP"]["first_member"](bad, extent)
    except zlib.error:
        return bad
    raise AssertionError("zlib accepted a bad member CRC")


def fixtures(lz4, zstd, decode):
    genuine, authored, positives = {}, {}, {}
    refusals = []
    zstd_reference = REFERENCE["ZSTD"]
    zstd_run = zstd_reference["ZSTD"]["run"]

    for name, (codec, producer) in PRODUCERS.items():
        for version in (1, 2):
            for optional, shape in ((True, "optional"), (False, "required")):
                label = f"{name}_v{version}_{shape}"
                case = native(ALL if optional else (False, False, False, True), optional, version,
                              reverse=not optional, compression=producer, write_page_checksum=optional)
                genuine[label] = positives[label] = case
                assert {meta[4][1] for _, meta, _, _ in NATIVE["V2"]["columns"](case[2])} == {codec}

    path = ".".join(NATIVE["PATH"])
    label = "native_independent_codecs"
    genuine[label] = positives[label] = native(ALL, True, 2, compression={
        f"{path}.lo": "ZSTD", f"{path}.hi": "GZIP"})
    assert [SNAPPY["column_codec"](genuine[label][2], (0, side)) for side in (0, 1)] == [6, 2]

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
        for key, source in chunks.items():
            codec = codecs[key]
            set_codec(footer, key, codec)
            encoded = []
            for frame in source:
                header, body = header_body(frame)
                levels, values, _, _ = parts(header, body)
                if header[1][1] == 3:
                    header[8][1][7] = TType.BOOL, bool(values)
                stored = compressors[codec](values) if values or header[1][1] == 0 else values
                encoded.append(encode(header, levels + stored, len(body)))
            chunks[key] = encoded
        return repack(wire, chunks, footer)

    _, earlier, cases, _, _, _ = BASE["fixtures"]()
    schema, groups, wire = cases["mixed_versions"]
    authored["uncompressed_reference"] = wire
    positives["uncompressed_reference"] = schema, groups, wire
    authored["mixed_child_cuts"] = reframe(wire)
    positives["mixed_child_cuts"] = schema, groups, authored["mixed_child_cuts"]

    bad_topology = authored["late_topology"] = reframe(earlier["late_presence"])
    trace = NATIVE["trace"]
    lhs, rhs = (trace(groups[1], ALL, side, optional_element=True) for side in (0, 1))
    shared = NATIVE["steps"](ALL)[2] + 1
    split = len(trace(groups[1][:2], ALL, 1, optional_element=True))
    slot = next(i for i in range(split, len(rhs)) if rhs[i][1:] == (shared, None))
    assert lhs[slot][0] == rhs[slot][0] and min(lhs[slot][1], shared) == shared
    point = NATIVE["point"]
    topology = (f".topology (.conflict {slot} {point(bad_topology, 1, 0, slot)} "
                f"{point(bad_topology, 1, 1, slot)} ({rhs[slot][0]}, {shared}) ({rhs[slot][0]}, {shared - 1}))")

    def patch(label, source, edit, *, key=LATE, ordinal=0):
        wire = positives[source][2]
        chunks = raw_chunks(wire)
        chunks[key][ordinal] = edit(*header_body(chunks[key][ordinal]))
        authored[label] = repack(wire, chunks)

    def change_payload(label, source, edit, cause, *, key=LATE, ordinal=0, crc=True):
        def frame(header, stored):
            levels, block, extent, compressed = parts(header, stored)
            assert compressed
            return encode(header, levels + edit(block, extent), header[2][1], crc=crc)

        patch(label, source, frame, key=key, ordinal=ordinal)
        refusals.append(Refusal(label, source, ordinal, cause, key=key))

    for name, (codec, _) in PRODUCERS.items():
        source = f"{name}_v2_optional"
        schema, groups, wire = positives[source]
        chunks = raw_chunks(wire)
        for key, stored in chunks.items():
            changed = []
            for page in stored:
                header, body = header_body(page)
                _, _, _, compressed = parts(header, body)
                changed.append(raw_bypass(header, body, decode=lambda block, extent: decode(codec, block, extent))
                               if compressed else page)
            chunks[key] = changed
        label = f"{name}_v2_bypass"
        authored[label] = repack(wire, chunks)
        positives[label] = schema, groups, authored[label]
        assert all(not parts(header, body)[3] for key in chunks for _, header, _, body in frames(authored[label], key))

        label = f"late_{name}_stored_crc"
        header, body = header_body(raw_chunks(wire)[LATE][0])
        levels, _, _, compressed = parts(header, body)
        assert compressed and levels
        patch(label, source, lambda h, b: encode(h, levels + b"\0", h[2][1], crc=False))
        checksum = f".checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(levels + b'\0')})"
        refusals.append(Refusal(label, source, 0, checksum))

    source = "lz4_v1_optional"

    def framed_lz4(block, extent):
        raw = decode(7, block, extent)
        framed = pa.Codec("lz4_frame").compress(raw).to_pybytes()
        assert framed.startswith(b"\x04\x22\x4d\x18")
        assert REFERENCE["LZ4"]["reference_decode"](lz4, framed, extent) is None
        return framed

    change_payload("late_framed_lz4", source, framed_lz4, ".payload (.malformed .lz4Raw)")
    patch("late_lz4_extent", source, lambda header, body: encode(header, body, header[2][1] + 1))
    refusals.append(Refusal("late_lz4_extent", source, 0, ".payload .outputSizeMismatch"))
    wire = genuine[source][2]
    footer = NATIVE["metadata"](wire)
    set_codec(footer, LATE, 5)
    authored["late_legacy_lz4"] = NATIVE["TWO"]["SCHEMA"]["pack"](wire, footer)

    def gzip_second_member(block, extent):
        second = zlib.compress(b"", wbits=31)
        changed = block + second
        assert REFERENCE["GZIP"]["first_member"](changed, extent)[1] == second
        return changed

    change_payload("late_gzip_second_member", "gzip_v2_optional", gzip_second_member, ".payload (.trailingInput .gzip)")
    change_payload("late_gzip_bad_trailer", "gzip_v1_optional", gzip_bad_crc,
                   ".payload (.malformed .gzip)", ordinal=1)
    source = "gzip_v2_optional"
    refusals.append(Refusal(source, source, 0, ".payload .gzipIncomplete",
                            key=(1, 0), caps=GZIP_ZERO, verify_prefix=False))

    def zstd_second_frame(block, _):
        changed = block + block
        assert zstd_reference["frame_info"](zstd, changed)[0] == len(block)
        return changed

    def zstd_dictionary(block, _):
        descriptor = block[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = block[:4] + bytes([descriptor | 1]) + block[5:at] + b"\x07" + block[at:]
        assert zstd_reference["frame_info"](zstd, changed)[4] == 7
        return changed

    source = "zstd_v2_optional"
    change_payload("late_zstd_second_frame", source, zstd_second_frame, ZSTD_FRAME.format(".trailingInput"))
    change_payload("late_zstd_dictionary", source, zstd_dictionary, ZSTD_FRAME.format("(.unsupportedDictionary 7)"))
    refusals.append(Refusal(source, source, 0, ZSTD_FRAME.format(".windowLimit"),
                            key=(1, 0), caps=ZSTD_ZERO, verify_prefix=False))

    source = "gzip_v2_optional"
    wire = genuine[source][2]
    lo, hi = next((lo, hi) for key, _, lo, hi in NATIVE["V2"]["columns"](wire) if key == LATE)
    totals_errors = {}
    for label, field, delta, stop in (("late_raw_total", 6, 1, hi), ("late_stored_total", 7, -1, hi - 1)):
        footer = NATIVE["metadata"](wire)
        column = THRIFT["column_metadata"](footer, *LATE)
        size = column[field][1]
        column[field] = TType.I64, size + delta
        authored[label] = NATIVE["TWO"]["SCHEMA"]["pack"](wire, footer)
        cause = f".rawSize {size + 1} {size}" if field == 6 else ".framing .payloadBounds"
        totals_errors[label] = f".chunk (.chunk {NATIVE['address'](*LATE)} ⟨{lo}, {stop}⟩ ({cause}))"

    dictionary = native(ALL, True, 2, compression="gzip", use_dictionary=True)[2]
    return genuine, authored, positives, dictionary, refusals, totals_errors, topology


def verify(folder):
    lz4, zstd, decode = REFERENCE["reference_codecs"](folder)
    genuine, authored, positives, dictionary, refusals, totals_errors, topology = fixtures(lz4, zstd, decode)
    originals = {label: case[2] for label, case in genuine.items()}
    files = originals | authored | {"parquet_dictionary": dictionary}
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code, entry, observations, counts = [LEAN.rsplit("set_option maxHeartbeats", 1)[0]], [], {}, Counter()
    caps = {"gzip_v2_bypass": GZIP_ZERO, "zstd_v2_bypass": ZSTD_ZERO}
    for label, (schema, groups, wire) in positives.items():
        commands, logical, columns, frame_counts = SNAPPY["source_commands"](
            label, schema, groups, wire, decode, checksums=not label.endswith("_required"), limits=caps.get(label, "{}"))
        observations[label] = schema, logical, columns
        if label == "mixed_child_cuts":
            pages = columns[1, 0][1]
            assert [page[-1][0][0] for page in pages[:3]] == [0, 2, 1]
            assert [frame[1][1][1] for frame in frames(wire, (1, 0))[:3]] == [0, 0, 0]
        counts.update(frame_counts)
        code.extend([f"set_option maxHeartbeats 2000000 in\nprivate def verify_{label} (folder : System.FilePath) : IO Unit := do",
                     *commands])
        entry.append(f"  verify_{label} folder")

    control = []

    def failure(label, reference, group, error, *, caps="{}", verify_prefix=True):
        control.append(f'  groupRefusal (← load folder "{label}") {group} {caps} ({error})')
        if verify_prefix:
            schema, logical, _ = observations[reference]
            prefix = IPC["batches_term"](schema, logical[:group])
            control.append(f'  checkFailure (← load folder "{label}") {caps} {prefix} (.group {group} ({error}))')

    for test in refusals:
        at, header, _, _ = frames(files[test.label], test.key)[test.ordinal]
        cursor = observations[test.original][2][test.key][1][test.ordinal][-3]
        cause = test.cause
        if header[1][1] == 3:
            cause = f".v2 ({cause})"
        elif not cause.startswith(".checksum"):
            cause = f".v1Payload ({cause})"
        error = (f".chunk (.page {NATIVE['address'](*test.key)} {test.ordinal} {at} "
                 f"{SNAPPY['triple'](cursor)} ({cause}))")
        failure(test.label, test.original, test.key[0], error, caps=test.caps, verify_prefix=test.verify_prefix)
    for label, cause in totals_errors.items():
        failure(label, "gzip_v2_optional", 1, cause)
    failure("late_legacy_lz4", "lz4_v1_optional", 1, f".binding (.column {NATIVE['address'](*LATE)} (.codec 5))")
    failure("late_topology", "mixed_child_cuts", 1, topology)
    schema, logical, _ = observations["gzip_v2_optional"]
    control.append(f'  checkRows (← load folder "parquet_dictionary") {IPC["batches_term"](schema, logical)}')

    code.extend(["private def controls (folder : System.FilePath) : IO Unit := do", *control,
                 'public def main (args : List String) : IO Unit := do',
                 '  let [folder] := args | throw (IO.userError "expected fixture directory")',
                 *entry, "  controls folder"])
    NATIVE["V2"]["run_lean"](folder, "TwoListStructCodecs.lean", code)

    ipc = {}
    for label, (schema, logical, _) in observations.items():
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            name = f"{label}_{selection}"
            output = ipc[name] = (folder / f"{name}.arrow").read_bytes()
            IPC["inspect_ipc"](output, projected, logical)
    for selection in ("field", "empty"):
        assert ipc[f"mixed_child_cuts_{selection}"] == ipc[f"uncompressed_reference_{selection}"]
        for name in PRODUCERS:
            assert ipc[f"{name}_v2_bypass_{selection}"] == ipc[f"{name}_v2_optional_{selection}"]
        assert ipc[f"native_independent_codecs_{selection}"] == ipc[f"zstd_v2_optional_{selection}"]
    print(f"Checked {len(positives)} sources, {counts['v1']} V1 and {counts['v2']} V2 frames, "
          f"{counts['v2_raw_words']} false-flag V2 suffixes with signed words, {len(ipc)} exact IPC streams "
          f"and {len(refusals) + len(totals_errors) + 2} typed controls")
    pins = NATIVE["fingerprints"]
    return {
        "reference": {"liblz4": REFERENCE["LZ4"]["PIN"], "libzstd": REFERENCE["ZSTD"]["ZSTD"]["PIN"],
                      "zlib": zlib.ZLIB_RUNTIME_VERSION},
        "genuine_parquet": pins(originals | {"parquet_dictionary": dictionary}),
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
