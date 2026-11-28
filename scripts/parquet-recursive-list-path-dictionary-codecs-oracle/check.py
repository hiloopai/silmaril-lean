"""Check compressed LIST-path dictionaries against original producer frames."""

from copy import deepcopy
from dataclasses import dataclass
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
DICT = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-dictionary-oracle/check.py"))
TWO = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-dictionary-codecs-oracle/check.py"))
MORE = TWO["MORE"]
V1, V2, FRAMES, EVENTS, GROUP, THRIFT, SCHEMA = (
    DICT[key] for key in ("V1", "V2", "FRAMES", "EVENTS", "GROUP", "THRIFT", "SCHEMA")
)
write, schema_for, samples, metadata, address, triple, fingerprints, source_commands, inspect_ipc = (
    DICT[key] for key in ("write", "schema_for", "samples", "metadata", "address", "triple",
                         "fingerprints", "source_commands", "inspect_ipc")
)
raw_chunks, header_body, encode, repack, original_frames = (
    DICT[key] for key in ("raw_chunks", "header_body", "encode", "repack", "original_frames")
)
GZIP_ZERO, ZSTD_ZERO, ZSTD_FRAME, REFERENCE, payload_parts = (
    TWO[key] for key in ("GZIP_ZERO", "ZSTD_ZERO", "ZSTD_FRAME", "REFERENCE", "payload_parts")
)
SNAPPY = DICT["BASE"]["SNAPPY"]
PRODUCERS = {"snappy": (1, "SNAPPY"), **MORE["PRODUCERS"]}

LEAN = DICT["LEAN"] + """
set_option maxRecDepth 32768

/-- Check the suffix path under a zero work budget after the dictionary is checked. -/
private def checkBypass (file : Bytes) (group : Nat) (limits : Chunk.Limits)
    (failure : Chunk.PageCause) (flaggedOrdinal : Nat) (flagged : Bool) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (Chunk.bind source.schema group)
  let read ← take (Chunk.read {} binding)
  let some page := read.pages[flaggedOrdinal - 1]? | throw (IO.userError "missing data frame")
  let .dataV2 header := page.frame.value.kind | throw (IO.userError "expected V2 data frame")
  unless header.isCompressed = flagged ∧ header.encoding = 8 do
    throw (IO.userError "expected original V2 dictionary flag and encoding")
  let plan := source.schema.plan
  let checked := Chunk.decodeDataPage limits plan (Chunk.wrappers plan) file page.frame page.start
    (binding.column.metadata.numValues.toNat - page.start.slots) binding.rowGroup.numRows.toNat
    binding.codec read.dictionary
  if flagged then
    deny failure checked
  else
    let decoded ← take checked
    unless decoded.sections = page.decoded.sections ∧ decoded.atoms = page.decoded.atoms ∧
        decoded.after = page.decoded.after do
      throw (IO.userError "raw index suffix differs at zero codec budget")
"""


@dataclass(frozen=True)
class Refusal:
    file: str
    reference: str
    ordinal: int
    cause: str
    group: int = 1
    limits: str = "{}"
    prefix: bool = False
    leading: bool = False


def data_encoding(header):
    return (header[8][1][4] if header[1][1] == 3 else header[5][1][2])[1]


def fixtures(lz4, zstd, decode):
    genuine, authored, positives, controls = {}, {}, {}, []
    for width in (32, 64):
        for depth in (2, 3, 6):
            nullable = (True,) * (depth + 1) if depth < 6 else tuple(i % 2 == 0 for i in range(depth + 1))
            schema, groups = schema_for(nullable, width), samples(nullable, width)
            # Put a long indexed row before the high-cardinality rows that trigger PLAIN fallback.
            leaves = groups[1][0] = deepcopy(groups[1][0])
            for _ in range(depth - 1):
                leaves = leaves[-1]
            leaves.extend([17, -9] * 96)
            groups[1] += [DICT["nested_row"](list(range(100 + i * 4, 104 + i * 4)), depth) for i in range(6)]
            for name, (codec, producer) in PRODUCERS.items():
                for page in (1, 2):
                    label = f"{name}_v{page}_{width}_d{depth}"
                    genuine[label] = write(schema, groups, compression=producer, use_dictionary=True,
                                           data_page_version=f"{page}.0", dictionary_pagesize_limit=64,
                                           data_page_size=64, max_rows_per_page=1, write_batch_size=1,
                                           write_page_checksum=depth != 6)
                    positives[label] = (schema, nullable, width, groups), [codec] * len(groups)

    def target(name, page):
        return f"{name}_v{page}_32_d3"

    source, _ = positives[target("snappy", 1)]
    schema, nullable, width, groups = source
    identity_rows = [*groups[0], DICT["nested_row"](list(range(50, 82)), len(nullable) - 1)]
    genuine["identity_origin"] = write(schema, [identity_rows], use_dictionary=True)
    sources = [("identity_origin", 0), (target("snappy", 2), 0), (target("lz4", 1), 1),
               (target("gzip", 2), 1), (target("zstd", 2), 1)]
    authored["mixed_groups"] = MORE["combine_groups"]([(genuine[label], group) for label, group in sources])
    mixed_rows = [identity_rows, *(positives[label][0][3][group] for label, group in sources[1:])]
    positives["mixed_groups"] = (schema, nullable, width, mixed_rows), [0, 1, 7, 2, 6]

    _, previous, cases, _ = DICT["fixtures"]()
    identity = previous["mixed_versions_fallback"]
    authored["identity_reframe"] = identity
    positives["identity_reframe"] = cases["mixed_versions_fallback"]
    footer = metadata(identity)
    chunks = raw_chunks(identity)
    for key, frames in chunks.items():
        THRIFT["column_metadata"](footer, *key)[4] = TType.I32, 1
        for ordinal, frame in enumerate(frames):
            header, body = header_body(frame)
            levels, suffix, extent, flag = payload_parts(header, body)
            if flag:
                frames[ordinal] = encode(header, levels + SNAPPY["snappy_encode"](suffix), len(levels) + extent)
    authored["snappy_reframe"] = repack(identity, chunks, footer)
    positives["snappy_reframe"] = positives["identity_reframe"][0], [1, 1]

    def patch(label, reference, ordinal, edit, group=1):
        wire = (genuine | authored)[reference]
        chunks = raw_chunks(wire)
        frames = chunks[group, 0]
        frames[ordinal] = edit(*header_body(frames[ordinal]))
        authored[label] = repack(wire, chunks)

    def patch_body(label, reference, ordinal, change, *, group=1, crc=True):
        def edit(header, body):
            levels, stored, extent, flag = payload_parts(header, body)
            assert flag
            return encode(header, levels + change(stored, extent), header[2][1], crc=crc)
        patch(label, reference, ordinal, edit, group)

    flagged, bypasses = {}, {}
    for name, (codec, _) in PRODUCERS.items():
        reference = target(name, 2)
        frames = original_frames(genuine[reference])
        ordinal = next(index for index, (_, header, _, body) in enumerate(frames)
                       if header[1][1] == 3 and data_encoding(header) == 8 and payload_parts(header, body)[3])
        flagged[name] = ordinal
        bypass = bypasses[name] = f"{name}_raw_bypass"
        patch(bypass, reference, ordinal, lambda h, b: SNAPPY["raw_bypass"](
            h, b, decode=lambda block, size: decode(codec, block, size)))
        positives[bypass] = positives[reference]

        bad_crc = f"late_{name}_dictionary_crc"
        patch_body(bad_crc, reference, 0, lambda _, __: b"\x80", crc=False)
        _, h, _, body = original_frames(authored[bad_crc])[0]
        cause = f".checksum (.mismatch {h[4][1] & 0xffffffff} {zlib.crc32(body)})"
        controls.append(Refusal(bad_crc, reference, 0, cause, leading=True, prefix=True))

    snappy = target("snappy", 1)
    patch_body("late_snappy_v1_trailing", snappy, 1, lambda stored, _: stored + b"\0")
    controls.append(Refusal("late_snappy_v1_trailing", snappy, 1,
                            ".v1Payload (.payload (.trailingInput .snappy))", prefix=True))
    patch_body("snappy_dictionary_trailing", snappy, 0, lambda stored, _: stored + b"\0")
    controls.append(Refusal("snappy_dictionary_trailing", snappy, 0,
                            ".payload (.trailingInput .snappy)", leading=True))

    lz4_source = target("lz4", 1)
    patch("lz4_dictionary_extent", lz4_source, 0, lambda h, b: encode(h, b, h[2][1] + 1))
    controls.append(Refusal("lz4_dictionary_extent", lz4_source, 0, ".payload .outputSizeMismatch", leading=True))
    _, _, _, body = original_frames(genuine[lz4_source])[0]
    controls.append(Refusal(lz4_source, lz4_source, 0, f".dictionaryByteLimit {len(body)}",
                            limits=f"{{ maxDictionaryBytes := {len(body) - 1} }}", leading=True))
    patch("lz4_dictionary_raw_cap", lz4_source, 0, lambda h, b: encode(h, b, h[3][1] + 1))
    controls.append(Refusal("lz4_dictionary_raw_cap", lz4_source, 0, f".dictionaryRawByteLimit {len(body) + 1}",
                            limits=f"{{ maxDictionaryBytes := {len(body)} }}", leading=True))
    lz4_v2 = target("lz4", 2)

    def lz4_tail(block, extent):
        changed = block + b"\0"
        assert MORE["LZ4"]["reference_decode"](lz4, changed, extent) is None
        return changed

    patch_body("late_lz4_v2_trailing", lz4_v2, flagged["lz4"], lz4_tail)
    controls.append(Refusal("late_lz4_v2_trailing", lz4_v2, flagged["lz4"],
                            ".v2 (.payload (.malformed .lz4Raw))", prefix=True))

    gzip = target("gzip", 2)
    patch_body("gzip_dictionary_trailer", gzip, 0,
               lambda block, _: block[:-8] + bytes([block[-8] ^ 1]) + block[-7:])
    controls.append(Refusal("gzip_dictionary_trailer", gzip, 0, ".payload (.malformed .gzip)", leading=True))
    def gzip_second_member(block, size):
        extra = zlib.compress(b"", wbits=31)
        assert TWO["GZIP"]["first_member"](block + extra, size)[1] == extra
        return block + extra

    patch_body("gzip_second_member", gzip, flagged["gzip"], gzip_second_member)
    controls.append(Refusal("gzip_second_member", gzip, flagged["gzip"], ".v2 (.payload (.trailingInput .gzip))"))
    controls.append(Refusal(gzip, gzip, 0, ".payload .gzipIncomplete", limits=GZIP_ZERO, leading=True))

    zstd_source = target("zstd", 2)
    controls.append(Refusal(zstd_source, zstd_source, 0, ZSTD_FRAME.format(".windowLimit"),
                            limits=ZSTD_ZERO, leading=True))

    def zstd_dict_id(block, _):
        descriptor = block[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = block[:4] + bytes([descriptor | 1]) + block[5:at] + b"\x07" + block[at:]
        assert MORE["ZSTD"]["frame_info"](zstd, changed)[4] == 7
        return changed

    patch_body("zstd_compression_dictionary", zstd_source, 0, zstd_dict_id)
    controls.append(Refusal("zstd_compression_dictionary", zstd_source, 0,
                            ZSTD_FRAME.format("(.unsupportedDictionary 7)"), leading=True))

    _, header, _, _ = original_frames(authored["mixed_groups"], 4)[0]
    local_count = header[7][1][1][1]
    _, earlier, _, _ = original_frames(authored["mixed_groups"], 0)[0]
    assert local_count < earlier[7][1][1][1] <= 255

    def bad_index(header, body):
        levels, _, _, flag = payload_parts(header, body)
        assert flag and header[8][1][4][1] == 8
        count, nulls = [header[8][1][key][1] for key in (1, 2)]
        indices = b"\x08" + TWO["DICT"]["varint"]((count - nulls) * 2) + bytes([local_count])
        compressed = MORE["ZSTD"]["ZSTD"]["run"](zstd, "compress", data=indices)
        assert decode(6, compressed, len(indices)) == indices
        return encode(header, levels + compressed, len(levels) + len(indices))

    patch("late_zstd_index", "mixed_groups", flagged["zstd"], bad_index, 4)
    controls.append(Refusal("late_zstd_index", "mixed_groups", flagged["zstd"],
                            f".dictionaryIndices (.outOfBounds {local_count})", group=4, prefix=True))

    def pack_metadata(label, wire, group, edit):
        footer = metadata(wire)
        edit(THRIFT["column_metadata"](footer, group, 0))
        authored[label] = SCHEMA["pack"](wire, footer)

    gzip_wire = genuine[gzip]
    first_data = original_frames(gzip_wire)[1][0]
    for label, wire in (("wrong_data_offset", gzip_wire),
                        ("crc_before_data_offset", authored["late_gzip_dictionary_crc"])):
        data = original_frames(wire)[1][0]
        pack_metadata(label, wire, 1, lambda meta: meta.update({9: (TType.I64, data + 1)}))
    controls.append(Refusal("wrong_data_offset", gzip, 1, f".dataOffset {first_data + 1} {first_data}",
                            leading=True, prefix=True))
    controls.append(Refusal("crc_before_data_offset", gzip, 0,
                            next(test.cause for test in controls if test.file == "late_gzip_dictionary_crc"),
                            leading=True))

    for label, field, delta in (("raw_total", 6, 1), ("stored_total", 7, -1)):
        pack_metadata(label, gzip_wire, 1, lambda meta: meta.update({field: (TType.I64, meta[field][1] + delta)}))
    pack_metadata("legacy_lz4", gzip_wire, 0, lambda meta: meta.update({4: (TType.I32, 5)}))
    pack_metadata("brotli_outside_profile", gzip_wire, 0, lambda meta: meta.update({4: (TType.I32, 4)}))
    pack_metadata("legacy_encoding_metadata", gzip_wire, 0,
                  lambda meta: meta.update({2: (TType.LIST, (TType.I32, [0, 3, 2]))}))

    def legacy_encoding(header, body):
        header[8][1][4] = TType.I32, 2
        return encode(header, body, header[2][1])

    patch("legacy_data_tag", gzip, flagged["gzip"], legacy_encoding)
    controls.append(Refusal("legacy_data_tag", gzip, flagged["gzip"], ".v2 (.v2Encoding 2)"))

    def legacy_dictionary_tag(header, body):
        header[7][1][2] = TType.I32, 2
        return encode(header, body, header[2][1])

    patch("legacy_dictionary_tag", gzip, 0, legacy_dictionary_tag)
    controls.append(Refusal("legacy_dictionary_tag", gzip, 0, ".dictionaryEncoding 2", leading=True))
    return genuine, authored, positives, controls, flagged, bypasses


def verify(folder):
    lz4, zstd, decode = MORE["reference_codecs"](folder)
    genuine, authored, positives, controls, flagged, bypasses = fixtures(lz4, zstd, decode)
    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code, entry, observed = [LEAN], [*V1["ENTRY"]], {}
    dictionaries_count = pages_count = raw_indices = compressed_indices = fallback_pages = 0
    for label, (case, codecs) in positives.items():
        captured, dictionaries, commands = source_commands(label, files[label], case, codecs, decode)
        observed[label] = captured
        assert list(dictionaries) == list(range(len(captured)))
        dictionaries_count += len(dictionaries)
        for group, (lo, hi, _, pages) in enumerate(captured):
            frames = list(FRAMES(files[label], lo, hi))[1:]
            tags = [data_encoding(header) for _, header, _, _ in frames]
            pages_count += len(pages)
            fallback_pages += tags.count(0)
            if label in genuine and group == 1:
                assert set(tags) == {0, 8} and tags == sorted(tags, reverse=True)
            for (_, header, _, body), tag in zip(frames, tags, strict=True):
                if header[1][1] == 3 and tag == 8:
                    if payload_parts(header, body)[3]:
                        compressed_indices += 1
                    else:
                        raw_indices += 1
        code.extend(commands)
        entry.append(f"  verify_{label} folder")

    for test in controls:
        (schema, nullable, width, groups), _ = positives[test.reference]
        column = address(len(nullable) - 1, test.group)
        offset = original_frames(files[test.file], test.group)[test.ordinal][0]
        if test.leading:
            error = f".dictionary {column} {test.ordinal} {offset} ({test.cause})"
        else:
            state = observed[test.reference][test.group][-1][test.ordinal - 1][-3]
            error = f".page {column} {test.ordinal} {offset} {triple(state)} ({test.cause})"
        entry.append(f'  refuse (← load folder "{test.file}") {test.group} {test.limits} ({error})')
        if test.prefix:
            entry.append(f'  sourceFailure (← load folder "{test.file}") {EVENTS["declarations"](schema)} '
                         f'{EVENTS["batch_terms"](groups[:test.group], width)} (.group {test.group} (.chunk ({error})))')

    gzip = "gzip_v2_32_d3"
    lo, hi, _, _ = observed[gzip][1]
    raw = THRIFT["column_metadata"](metadata(files[gzip]), *GROUP)[6][1]
    entry.extend([
        f'  refuse (← load folder "raw_total") 1 {{}} (.chunk {address(3, 1)} ⟨{lo}, {hi}⟩ (.rawSize {raw + 1} {raw}))',
        f'  refuse (← load folder "stored_total") 1 {{}} (.chunk {address(3, 1)} ⟨{lo}, {hi - 1}⟩ (.framing .payloadBounds))',
        f'  refuseBinding (← load folder "legacy_lz4") (.column {address(3, 0)} (.codec 5))',
        f'  refuseBinding (← load folder "brotli_outside_profile") (.column {address(3, 0)} (.codec 4))',
        f'  refuseBinding (← load folder "legacy_encoding_metadata") (.column {address(3, 0)} (.encodings [0, 3, 2]))',
    ])
    for name, limits, failure in (
        ("gzip", GZIP_ZERO, ".v2 (.payload .gzipIncomplete)"),
        ("zstd", ZSTD_ZERO, f'.v2 ({ZSTD_FRAME.format(".windowLimit")})'),
    ):
        for label, flag in ((f"{name}_v2_32_d3", "true"), (bypasses[name], "false")):
            entry.append(f'  checkBypass (← load folder "{label}") 1 {limits} ({failure}) {flagged[name]} {flag}')
    V2["run_lean"](folder, "ListPathDictionaryCodecs.lean", code + entry)

    emitted = {}
    for label, ((schema, _, _, groups), _) in positives.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            emitted[name] = (folder / f"{name}.arrow").read_bytes()
            inspect_ipc(emitted[name], schema, groups, selection)
    equivalent = [(label, f"{name}_v2_32_d3") for name, label in bypasses.items()]
    equivalent.append(("snappy_reframe", "identity_reframe"))
    for actual, original in equivalent:
        for selection in ("field", "empty"):
            assert emitted[f"{actual}_{selection}"] == emitted[f"{original}_{selection}"]
    print(f"Checked {len(positives)} inputs, {dictionaries_count} dictionaries, {pages_count} data frames "
          f"({fallback_pages} PLAIN fallback), {raw_indices} raw and {compressed_indices} compressed V2 "
          f"index suffixes, {len(emitted)} exact IPC streams and {len(controls) + 5} typed refusals")
    return {"reference": REFERENCE, "genuine_parquet": fingerprints(genuine),
            "authored_parquet": fingerprints(authored), "lean_ipc": fingerprints(emitted)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for key, value in captured.items():
        assert value == pins[key], f"{key} fixture pins changed"


if __name__ == "__main__":
    main()
