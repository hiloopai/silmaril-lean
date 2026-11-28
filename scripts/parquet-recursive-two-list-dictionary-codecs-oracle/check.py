"""Check original two-LIST dictionary and fallback payloads against independent codecs."""

from dataclasses import dataclass
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
DICT = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-dictionary-oracle/check.py"))
MORE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-more-codecs-oracle/check.py"))
(
    BASE, V2, THRIFT, MIXED, SCHEMA, IPC, PATH, I32, I64, GROUP, NULLABLE, raw_chunks, header_body,
    encode, repack, original_frames,
) = (DICT[key] for key in (
    "BASE", "V2", "THRIFT", "MIXED", "SCHEMA", "IPC", "PATH", "I32", "I64", "GROUP", "NULLABLE",
    "raw_chunks", "header_body", "encode", "repack", "original_frames",
))
LZ4, GZIP, ZSTD, PRODUCERS, TAGS, GZIP_ZERO, ZSTD_ZERO, ZSTD_FRAME = (
    MORE[key] for key in ("LZ4", "GZIP", "ZSTD", "PRODUCERS", "TAGS", "GZIP_ZERO", "ZSTD_ZERO", "ZSTD_FRAME")
)

REFERENCE = {"liblz4": LZ4["PIN"], "libzstd": ZSTD["ZSTD"]["PIN"], "zlib": zlib.ZLIB_RUNTIME_VERSION}

LEAN = DICT["LEAN"] + """
private def checkWorkBypass (file : Bytes) (group : Nat) (limits : Limits)
    (expected : PageCause) (expectedCompressed : Nat) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (Chunk.bind source.schema group)
  let seen ← take (read {} binding)
  let some dictionary := seen.dictionary | throw (IO.userError "expected checked original dictionary")
  let mut compressed := 0
  for page in seen.pages do
    let .dataV2 info := page.frame.value.kind | throw (IO.userError "expected original V2 data")
    let checked := decodeDataPage limits source.schema.plan file page.frame page.start
      (binding.column.metadata.numValues.toNat - page.start.slots) binding.rowGroup.numRows.toNat
      binding.codec (some dictionary)
    if info.isCompressed then
      compressed := compressed + 1
      deny expected checked
    else
      let decoded ← take checked
      unless decoded.levels = page.decoded.levels ∧ decoded.words = page.decoded.words ∧
          decoded.after = page.decoded.after do
        throw (IO.userError "raw index suffix differs at zero codec budgets")
  unless compressed = expectedCompressed do
    throw (IO.userError "original compressed flag count differs")
"""


@dataclass(frozen=True)
class Refusal:
    file: str
    reference: str
    ordinal: int
    cause: str
    group: int = 1
    limits: str = "{}"
    readback: bool = False


def payload_parts(header, body):
    if header[1][1] == 2:
        return b"", body, header[2][1], True
    return MORE["parts"](header, body)


def fixtures(lz4, zstd, decode):
    genuine, edited, positives, controls = {}, {}, {}, []
    for name, (codec, producer) in PRODUCERS.items():
        for width in (32, 64):
            rows = BASE["samples"](NULLABLE, width)
            rows[1][-1][0].extend([7, -9] * 96)
            rows.append([None, [], [None, [], [None]]])
            schema = BASE["schema_for"](NULLABLE, width)
            for page_version in (1, 2):
                label = f"{name}_v{page_version}_{width}"
                genuine[label] = BASE["write"](schema, rows, compression=producer, use_dictionary=True,
                                                data_page_version=f"{page_version}.0")
                positives[label] = width, rows, [codec] * len(rows)
        for page_version, width in ((1, 32), (2, 64)):
            rows = BASE["samples"](NULLABLE, width)
            rows[1] = [[[i + 100, -i - 3], [], None, [None]] for i in range(16)]
            rows[1][-1][0].extend([17] * 96)
            label = f"{name}_fallback_v{page_version}"
            genuine[label] = BASE["write"](BASE["schema_for"](NULLABLE, width), rows, compression=producer,
                                            data_page_version=f"{page_version}.0", use_dictionary=True,
                                            dictionary_pagesize_limit=48)
            positives[label] = width, rows, [codec] * len(rows)

    previous, _, shapes, *_ = DICT["fixtures"]()
    origins = ((previous["native_0_v1_32"], 0), (genuine["lz4_fallback_v1"], 1),
               (previous["native_1_v2_32"], 0), (genuine["gzip_v2_32"], 1), (genuine["zstd_v2_32"], 1))
    edited["mixed_groups"] = MORE["combine_groups"](origins)
    mixed_rows = [shapes["native_0_v1_32"][1][0], positives["lz4_fallback_v1"][1][1],
                  shapes["native_1_v2_32"][1][0], positives["gzip_v2_32"][1][1], positives["zstd_v2_32"][1][1]]
    positives["mixed_groups"] = 32, mixed_rows, [0, 7, 1, 2, 6]

    def patch(label, source, ordinal, edit, *, group=1):
        wire = (genuine | edited)[source]
        chunks = raw_chunks(wire)
        frames = chunks[group, 0]
        frames[ordinal] = edit(*header_body(frames[ordinal]))
        edited[label] = repack(wire, chunks)

    def change_payload(label, source, ordinal, edit, *, group=1, crc=True):
        def change(header, body):
            levels, stored, expected, compressed = payload_parts(header, body)
            assert compressed
            return encode(header, levels + edit(stored, expected), header[2][1], crc=crc)
        patch(label, source, ordinal, change, group=group)

    raw_cases = {}
    targets = {}
    for name, (codec, _) in PRODUCERS.items():
        source = f"{name}_v2_32"
        wire = genuine[source]
        chunks = raw_chunks(wire)
        data = chunks[GROUP]
        flagged = [index for index, page in enumerate(data[1:], 1)
                   if payload_parts(*header_body(page))[3]]
        assert len(flagged) == 1
        target, = flagged
        header, body = header_body(data[target])
        assert header[8][1][4][1] == 8
        targets[name] = target
        bypass = DICT["SNAPPY"]["SNAPPY"]["raw_bypass"](
            header, body, decode=lambda stored, extent: decode(codec, stored, extent))
        data[target] = bypass
        label = f"{name}_raw_bypass"
        edited[label] = repack(wire, chunks)
        positives[label] = positives[source]
        raw_cases[name] = label

        for version in (1, 2):
            reference = f"{name}_v{version}_32"
            fixture = f"{name}_v{version}_dictionary_crc"
            change_payload(fixture, reference, 0, lambda _, __: b"\x80", crc=False)
            _, before, _, corrupted = original_frames(edited[fixture])[0]
            crc = f".dictionary (.checksum (.mismatch {before[4][1] & 0xffffffff} {zlib.crc32(corrupted)}))"
            controls.append(Refusal(fixture, reference, 0, crc))

    def lz4_tail(block, extent):
        changed = block + b"\0"
        assert LZ4["reference_decode"](lz4, changed, extent) is None
        return changed

    selected = targets["lz4"]
    change_payload("late_lz4_block", "lz4_v2_32", selected, lz4_tail)
    controls.append(Refusal("late_lz4_block", "lz4_v2_32", selected,
                            ".v2 (.payload (.malformed .lz4Raw))", readback=True))
    patch("lz4_dictionary_extent", "lz4_v1_32", 0, lambda header, body: encode(header, body, header[2][1] + 1))
    controls.append(Refusal("lz4_dictionary_extent", "lz4_v1_32", 0, ".dictionary (.payload .outputSizeMismatch)"))
    _, header, _, stored = original_frames(genuine["lz4_v2_64"])[0]
    assert len(stored) < header[2][1]
    controls.append(Refusal("lz4_v2_64", "lz4_v2_64", 0,
                            f".dictionary (.dictionaryRawByteLimit {header[2][1]})",
                            limits=f"{{ maxDictionaryBytes := {len(stored)} }}"))

    def gzip_trailer(member, size):
        corrupted = member[:-8] + bytes([member[-8] ^ 1]) + member[-7:]
        try:
            GZIP["first_member"](corrupted, size)
        except zlib.error:
            return corrupted
        raise AssertionError("zlib accepted the changed member CRC")

    def gzip_second(member, size):
        extra = zlib.compress(b"", wbits=31)
        assert GZIP["first_member"](member + extra, size)[1] == extra
        return member + extra

    change_payload("late_gzip_dictionary_trailer", "gzip_v1_32", 0, gzip_trailer)
    controls.append(Refusal("late_gzip_dictionary_trailer", "gzip_v1_32", 0,
                            ".dictionary (.payload (.malformed .gzip))", readback=True))
    selected = targets["gzip"]
    change_payload("gzip_second_member", "gzip_v2_32", selected, gzip_second)
    controls.append(Refusal("gzip_second_member", "gzip_v2_32", selected, ".v2 (.payload (.trailingInput .gzip))"))
    controls.append(Refusal("gzip_v2_32", "gzip_v2_32", 0, ".dictionary (.payload .gzipIncomplete)", limits=GZIP_ZERO))

    def zstd_checksums(frame, size):
        raw = decode(6, frame, size)
        checked = ZSTD["ZSTD"]["run"](zstd, "compress-checksum", data=raw)
        assert ZSTD["frame_info"](zstd, checked)[5] == 1 and decode(6, checked, size) == raw
        return checked

    selected = targets["zstd"]
    change_payload("zstd_dictionary_checksum", "mixed_groups", 0, zstd_checksums, group=4)
    change_payload("mixed_checksums", "zstd_dictionary_checksum", selected, zstd_checksums, group=4)
    # Only the complete two-frame edit is a separate fixture.
    del edited["zstd_dictionary_checksum"]
    positives["mixed_checksums"] = positives["mixed_groups"]

    def corrupt_zstd_checksum(frame, size):
        changed = frame[:-1] + bytes([frame[-1] ^ 1])
        rejected = subprocess.run([zstd, "decode", str(size)], input=changed, capture_output=True, check=False)
        assert rejected.returncode == 3
        return changed

    change_payload("late_zstd_checksum", "mixed_checksums", selected, corrupt_zstd_checksum, group=4)
    controls.append(Refusal("late_zstd_checksum", "mixed_checksums", selected,
                            f'.v2 ({ZSTD_FRAME.format(".checksumMismatch")})', group=4, readback=True))

    original = edited["mixed_groups"]
    _, header, _, stored = original_frames(original, (4, 0))[selected]
    _, defs, _ = DICT["sections_v2"](header[8][1], stored, 2, 5)
    local_count = original_frames(original, (4, 0))[0][1][7][1][1][1]
    other_count = original_frames(original, (1, 0))[0][1][7][1][1][1]
    assert local_count < other_count <= 255
    outside = b"\x08" + DICT["varint"](defs.count(5) * 2) + bytes([local_count])
    def invalid_index(header, body):
        levels, _, _, flagged = payload_parts(header, body)
        assert flagged
        encoded = ZSTD["ZSTD"]["run"](zstd, "compress", data=outside)
        assert decode(6, encoded, len(outside)) == outside
        return encode(header, levels + encoded, len(levels) + len(outside))

    patch("late_zstd_index", "mixed_groups", selected, invalid_index, group=4)
    controls.append(Refusal("late_zstd_index", "mixed_groups", selected,
                            f".dictionaryIndices (.outOfBounds {local_count})", group=4, readback=True))

    def zstd_dictionary_id(frame, _):
        descriptor = frame[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = frame[:4] + bytes([descriptor | 1]) + frame[5:at] + b"\x07" + frame[at:]
        assert ZSTD["frame_info"](zstd, changed)[4] == 7
        return changed

    change_payload("zstd_compression_dictionary", "zstd_v1_32", 0, zstd_dictionary_id)
    controls.append(Refusal("zstd_compression_dictionary", "zstd_v1_32", 0,
                            f'.dictionary ({ZSTD_FRAME.format("(.unsupportedDictionary 7)")})'))
    controls.append(Refusal("zstd_v2_32", "zstd_v2_32", 0,
                            f'.dictionary ({ZSTD_FRAME.format(".windowLimit")})', limits=ZSTD_ZERO))

    wire = genuine["gzip_v2_32"]
    for label, field, delta in (("raw_total", 6, 1), ("stored_total", 7, -1)):
        footer = MIXED["metadata"](wire)
        metadata = THRIFT["column_metadata"](footer, *GROUP)
        metadata[field] = I64, metadata[field][1] + delta
        edited[label] = SCHEMA["pack"](wire, footer)
    return genuine, edited, positives, controls, raw_cases


def verify(scratch):
    lz4, zstd, decode = MORE["reference_codecs"](scratch)
    genuine, edited, positives, controls, raw_cases = fixtures(lz4, zstd, decode)
    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    code = [LEAN, *BASE["V1"]["ENTRY"]]
    observed, dictionaries, frames, raw_indices, compressed_indices = {}, 0, 0, 0, 0
    for label, (width, rows, codecs) in positives.items():
        wire = files[label]
        captured = list(DICT["inspect"](wire, width, rows, codecs, decode_block=decode))
        observed[label] = captured
        for group, lo, hi, end, dictionary, pages, raw_bytes in captured:
            at, payload, stop, crc, entries = dictionary
            terms = BASE["lst"](BASE["checked_page_term"]((page, v2), NULLABLE, width, tag)
                                for page, v2, tag in pages)
            code.append(f'  checkChunk (← load folder "{label}") {group} [true, true, true] (1, 3, 5) '
                        f'.int{width} ⟨{lo}, {hi}⟩ {BASE["state_term"](end)} {terms} .{TAGS[codecs[group]]}')
            words = BASE["lst"](f"(.int{width} ({entry}))" for entry in entries)
            code.append(f'  checkDictionary (← load folder "{label}") {group} ({at}, {payload}, {stop}) {crc} '
                        f'{words} {raw_bytes} {hi-lo}')
            dictionaries += 1
            frames += len(pages)
            raw_indices += sum(v2 is not None and not v2[-1] and encoding == 8 for _, v2, encoding in pages)
            compressed_indices += sum(v2 is not None and v2[-1] and encoding == 8 for _, v2, encoding in pages)
            if group == 1 and "_fallback_" in label:
                tags = [tag for _, _, tag in pages]
                assert set(tags) == {0, 8} and tags == sorted(tags, reverse=True)
                if label.endswith("v2"):
                    assert any(v2[-1] and encoding == 0 for _, v2, encoding in pages)
            if group == 1 and label.endswith("_raw_bypass"):
                assert all(not v2[-1] for _, v2, _ in pages)
        fields, batches = IPC["observation"](wire, width)
        code.append(f'  checkFile folder "{label}" (← load folder "{label}") {fields} {batches}')

    for name, limits, failure in (
        ("gzip", GZIP_ZERO, ".v2 (.payload .gzipIncomplete)"),
        ("zstd", ZSTD_ZERO, f'.v2 ({ZSTD_FRAME.format(".windowLimit")})'),
    ):
        code.append(f'  checkWorkBypass (← load folder "{name}_v2_32") 1 {limits} ({failure}) 1')
        code.append(f'  checkWorkBypass (← load folder "{raw_cases[name]}") 1 {limits} ({failure}) 0')

    for test in controls:
        frame = original_frames(files[test.file], (test.group, 0))[test.ordinal]
        pages = observed[test.reference][test.group][5]
        before = (0, 0, 0) if test.ordinal == 0 else pages[test.ordinal - 1][0][4]
        address = f"⟨{test.group}, 0, {json.dumps(PATH)}⟩"
        error = f'.page {address} {test.ordinal} {frame[0]} {BASE["state_term"](before)} ({test.cause})'
        code.append(f'  refuse (← load folder "{test.file}") {test.group} {test.limits} ({error})')
        if test.readback:
            fields, batches = IPC["observation"](files[test.reference], 32, prefix=test.group)
            code.append(f'  sourceFailure (← load folder "{test.file}") {fields} {batches} '
                        f'(.group {test.group} (.chunk ({error})))')

    _, lo, hi, _, _, _, raw_size = observed["gzip_v2_32"][1]
    address = f"⟨1, 0, {json.dumps(PATH)}⟩"
    code.extend([
        f'  refuse (← load folder "raw_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi}⟩ '
        f'(.uncompressedSize {raw_size + 1} {raw_size}))',
        f'  refuse (← load folder "stored_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi - 1}⟩ (.framing .payloadBounds))',
    ])
    V2["run_lean"](scratch, "TwoListDictionaryCodecs.lean", code)
    emitted = BASE["readback"](scratch, {key: (NULLABLE, width, rows) for key, (width, rows, _) in positives.items()})
    for label, source in [(label, f"{name}_v2_32") for name, label in raw_cases.items()] + [
        ("mixed_checksums", "mixed_groups"),
    ]:
        for selection in ("field", "empty"):
            assert emitted[f"{label}_{selection}"] == emitted[f"{source}_{selection}"]

    print(f"Checked {dictionaries} dictionaries, {frames} data frames, {raw_indices} raw and "
          f"{compressed_indices} compressed V2 index suffixes, {len(emitted)} IPC streams through exact EOS "
          f"and {len(controls) + 2} typed refusals")
    return {group: BASE["fingerprints"](items)
            for group, items in (("genuine", genuine), ("authored", edited), ("lean_ipc", emitted))}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    assert pins["reference"] == REFERENCE
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, fixtures in captured.items():
        assert fixtures == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
