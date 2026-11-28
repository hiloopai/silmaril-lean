"""Independently inspect original two-LIST LZ4_RAW, GZIP and Zstd pages."""

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
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-snappy-oracle/check.py"))
LZ4 = runpy.run_path(str(HERE.parent / "lz4-raw-oracle/check.py"))
GZIP = runpy.run_path(str(HERE.parent / "parquet-recursive-gzip-oracle/check.py"))
ZSTD = runpy.run_path(str(HERE.parent / "parquet-recursive-zstd-oracle/check.py"))
BASE, V2, THRIFT, MIXED, SCHEMA, IPC, PATH, I32, I64 = (
    SNAPPY[key] for key in ("BASE", "V2", "THRIFT", "MIXED", "SCHEMA", "IPC", "PATH", "I32", "I64")
)
raw_chunks, header_body, encode, repack, original_frames = (
    SNAPPY[key] for key in ("raw_chunks", "header_body", "encode", "repack", "original_frames")
)
parts = ZSTD["parts"]
SAMPLES = (True, True, True)
PRODUCERS = {"lz4": (7, "LZ4"), "gzip": (2, "GZIP"), "zstd": (6, "ZSTD")}
TAGS = {0: "uncompressed", 1: "snappy", 2: "gzip", 6: "zstd", 7: "lz4Raw"}
GZIP_ZERO = "{ gzipCalls := 0 }"
ZSTD_ZERO = "{ zstd := { window := 0, commandsPerBlock := 0 } }"
ZSTD_FRAME = ".zstd (.frame (.frame {}))"

LEAN = SNAPPY["LEAN"] + """
private def refuseBinding (file : Bytes) (expected : BindError) : IO Unit := do
  let source ← take (openFile {} file)
  deny expected (Chunk.bind source.schema 0)
"""


@dataclass(frozen=True)
class Refusal:
    file: str
    reference: str
    version: int
    cause: str
    group: int = 1
    ordinal: int = 1
    limits: str = "{}"
    readback: bool = False


def reference_codecs(scratch):
    lz4 = LZ4["build_reference"](scratch)
    zstd = ZSTD["ZSTD"]["build_reference"](scratch)

    def decode(codec, stored, size):
        if codec == 7:
            decoded = LZ4["reference_decode"](lz4, stored, size)
            assert decoded is not None and len(decoded) == size
            return decoded
        if codec == 2:
            return GZIP["decode_block"](codec, stored, size)
        if codec == 6:
            return ZSTD["decode_frame"](zstd, stored, size)
        assert codec == 1
        return SNAPPY["expand"](stored, size)

    return lz4, zstd, decode


def combine_groups(origins):
    """Splice exact producer frames with relocated original column metadata."""
    footer = MIXED["metadata"](origins[0][0])
    groups = []
    chunks = {}
    for output, (wire, original) in enumerate(origins):
        source = MIXED["metadata"](wire)
        groups.append(THRIFT["list_field"](source, 4)[original])
        chunks[output, 0] = raw_chunks(wire)[original, 0]
    footer[3] = I64, sum(group[3][1] for group in groups)
    footer[4] = TType.LIST, (TType.STRUCT, groups)
    output = repack(origins[0][0], chunks, footer)
    assert raw_chunks(output) == chunks
    return output


def fixtures(lz4, zstd, decode):
    genuine, edited, positives, controls = {}, {}, {}, []
    for width in (32, 64):
        rows = BASE["samples"](SAMPLES, width)
        rows[1][-1][0].extend([17] * 96)
        schema = BASE["schema_for"](SAMPLES, width)
        for name, (codec, producer) in PRODUCERS.items():
            for version in (1, 2):
                label = f"{name}_v{version}_{width}"
                genuine[label] = BASE["write"](schema, rows, compression=producer, data_page_version=f"{version}.0")
                positives[label] = width, rows, [codec] * len(rows)
                assert all(meta[4][1] == codec for _, meta, _, _ in V2["columns"](genuine[label]))
                frames = original_frames(genuine[label])
                assert len(frames) == 2 and parts(frames[1][1], frames[1][3])[3]

    origin_rows = BASE["samples"](SAMPLES, 32)
    schema = BASE["schema_for"](SAMPLES, 32)
    for label, codec, groups in (("identity_origin", "NONE", [origin_rows[0][:3]]),
                                 ("snappy_origin", "SNAPPY", [origin_rows[0][:2]])):
        genuine[label] = BASE["write"](schema, groups, compression=codec)
    selections = [("identity_origin", 0), ("lz4_v1_32", 1), ("snappy_origin", 0),
                  ("gzip_v2_32", 1), ("zstd_v2_32", 1)]
    edited["mixed_groups"] = combine_groups([(genuine[label], group) for label, group in selections])
    mixed_rows = [origin_rows[0][:3], positives["lz4_v1_32"][1][1], origin_rows[0][:2],
                  positives["gzip_v2_32"][1][1], positives["zstd_v2_32"][1][1]]
    positives["mixed_groups"] = 32, mixed_rows, [0, 7, 1, 2, 6]

    def patch(label, source, *, group=1, ordinal=1, edit):
        wire = (genuine | edited)[source]
        chunks = raw_chunks(wire)
        frames = chunks[group, 0]
        frames[ordinal] = edit(*header_body(frames[ordinal]))
        edited[label] = repack(wire, chunks)

    def edit_payload(label, source, change, *, group=1, crc=True):
        def edit(header, body):
            levels, stored, extent, flag = parts(header, body)
            assert flag
            return encode(header, levels + change(stored, extent), header[2][1], crc=crc)
        patch(label, source, group=group, edit=edit)

    for name, (codec, _) in PRODUCERS.items():
        for version in (1, 2):
            source = f"{name}_v{version}_32"
            _, header, _, body = original_frames(genuine[source])[1]
            raw_size, stored_size = header[2][1], len(body)
            before = original_frames(genuine[source])[:-1]
            assert stored_size < raw_size and all(max(h[2][1], len(b)) < stored_size for _, h, _, b in before)
            output = ".payload .outputLimit"
            if name == "zstd" and version == 1:
                output = ".zstd (.scalar (.payload .outputLimit))"
            controls.append(Refusal(source, source, version, ".checksum .byteLimit",
                                    limits=f"{{ maxBodyBytes := {stored_size - 1} }}"))
            controls.append(Refusal(source, source, version, output, limits=f"{{ maxBodyBytes := {stored_size} }}"))

            label = f"{name}_v{version}_stored_crc"
            edit_payload(label, source, lambda stored, size: b"\0", crc=False)
            _, altered, _, edited_body = original_frames(edited[label])[1]
            crc = f".checksum (.mismatch {altered[4][1] & 0xffffffff} {zlib.crc32(edited_body)})"
            controls.append(Refusal(label, source, version, crc))

        source = f"{name}_v2_32"
        label = f"{name}_raw_bypass"
        editor = lambda header, body: SNAPPY["raw_bypass"](header, body, decode=lambda stored, n: decode(codec, stored, n))
        patch(label, source, edit=editor)
        positives[label] = positives[source]
        assert all(not parts(header, body)[3] for _, header, _, body in original_frames(edited[label]))

    # Exact raw-block consumption and a separately addressed extent failure.
    def lz4_tail(stored, extent):
        changed = stored + b"\0"
        assert LZ4["reference_decode"](lz4, changed, extent) is None
        return changed

    edit_payload("late_lz4_tail", "lz4_v2_32", lz4_tail)
    controls.append(Refusal("late_lz4_tail", "lz4_v2_32", 2, ".payload (.malformed .lz4Raw)", readback=True))
    patch("lz4_extent", "lz4_v1_32", edit=lambda header, body: encode(header, body, header[2][1] + 1))
    controls.append(Refusal("lz4_extent", "lz4_v1_32", 1, ".payload .outputSizeMismatch"))
    footer = MIXED["metadata"](genuine["lz4_v1_32"])
    THRIFT["column_metadata"](footer, 0, 0)[4] = I32, 5
    edited["legacy_lz4"] = SCHEMA["pack"](genuine["lz4_v1_32"], footer)

    def gzip_trailer(member, size):
        corrupted = member[:-8] + bytes([member[-8] ^ 1]) + member[-7:]
        try:
            GZIP["first_member"](corrupted, size)
        except zlib.error:
            return corrupted
        raise AssertionError("zlib accepted the corrupted member CRC")

    def gzip_extra(member, size, extra):
        assert GZIP["first_member"](member + extra, size)[1] == extra
        return member + extra

    edit_payload("late_gzip_trailer", "gzip_v1_32", gzip_trailer)
    controls.append(Refusal("late_gzip_trailer", "gzip_v1_32", 1, ".payload (.malformed .gzip)", readback=True))
    for label, extra in (("gzip_trailing", b"\0"), ("gzip_second_member", zlib.compress(b"", wbits=31))):
        edit_payload(label, "gzip_v2_32", lambda stored, size: gzip_extra(stored, size, extra))
        controls.append(Refusal(label, "gzip_v2_32", 2, ".payload (.trailingInput .gzip)"))
    controls.append(Refusal("gzip_v2_32", "gzip_v2_32", 2, ".payload .gzipIncomplete", limits=GZIP_ZERO))

    def checksummed(frame, size):
        raw = decode(6, frame, size)
        checked = ZSTD["ZSTD"]["run"](zstd, "compress-checksum", data=raw)
        assert ZSTD["frame_info"](zstd, checked)[5] == 1 and decode(6, checked, size) == raw
        return checked

    edit_payload("zstd_checksums", "mixed_groups", checksummed, group=4)
    positives["zstd_checksums"] = positives["mixed_groups"]

    def corrupt_checksum(frame, size):
        assert len(decode(6, frame, size)) == size
        changed = frame[:-1] + bytes([frame[-1] ^ 1])
        rejected = subprocess.run([zstd, "decode", str(size)], input=changed, capture_output=True, check=False)
        assert rejected.returncode == 3
        return changed

    edit_payload("late_zstd_checksum", "zstd_checksums", corrupt_checksum, group=4)
    controls.append(Refusal("late_zstd_checksum", "zstd_checksums", 2, ZSTD_FRAME.format(".checksumMismatch"),
                            group=4, readback=True))

    def zstd_second_frame(frame, _):
        changed = frame + frame
        assert ZSTD["frame_info"](zstd, changed)[0] == len(frame) < len(changed)
        return changed

    def zstd_dictionary(frame, _):
        descriptor = frame[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = frame[:4] + bytes([descriptor | 1]) + frame[5:at] + b"\x07" + frame[at:]
        assert ZSTD["frame_info"](zstd, changed)[4] == 7
        return changed

    for label, change, cause in (
        ("zstd_second_frame", zstd_second_frame, ".trailingInput"),
        ("zstd_dictionary", zstd_dictionary, "(.unsupportedDictionary 7)"),
    ):
        edit_payload(label, "zstd_v2_32", change)
        controls.append(Refusal(label, "zstd_v2_32", 2, ZSTD_FRAME.format(cause)))
    controls.extend([
        Refusal("zstd_v2_32", "zstd_v2_32", 2, ZSTD_FRAME.format(".windowLimit"), limits=ZSTD_ZERO),
        Refusal("zstd_v2_32", "zstd_v2_32", 2,
                ".zstd (.frame (.compressed (.block (.tables (.prefix .sequenceLimit)))))",
                limits="{ zstd := { ({} : Limits).zstd with commandsPerBlock := 0 } }"),
    ])

    # The modified original footer size has no effect on the stored frames.
    wire = genuine["gzip_v2_32"]
    footer = MIXED["metadata"](wire)
    metadata = THRIFT["column_metadata"](footer, 1, 0)
    metadata[6] = I64, metadata[6][1] + 1
    edited["gzip_raw_total"] = SCHEMA["pack"](wire, footer)
    footer = MIXED["metadata"](wire)
    metadata = THRIFT["column_metadata"](footer, 1, 0)
    metadata[7] = I64, metadata[7][1] - 1
    edited["gzip_stored_total"] = SCHEMA["pack"](wire, footer)
    return genuine, edited, positives, controls


def verify(scratch):
    lz4, zstd, decode = reference_codecs(scratch)
    genuine, edited, positives, controls = fixtures(lz4, zstd, decode)
    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    code = [LEAN, *BASE["V1"]["ENTRY"]]
    observed, total, raw_v2 = {}, 0, 0
    for label, (width, rows, codecs) in positives.items():
        wire = files[label]
        observed[label] = list(BASE["inspect"](wire, SAMPLES, width, rows, codecs=codecs, expand=decode))
        for group, lo, hi, end, pages in observed[label]:
            codec = codecs[group]
            tag = TAGS[codec]
            terms = BASE["lst"](BASE["checked_page_term"](page, SAMPLES, width) for page in pages)
            code.append(f'  checkChunk (← load folder "{label}") {group} [true, true, true] (1, 3, 5) '
                        f'.int{width} ⟨{lo}, {hi}⟩ {BASE["state_term"](end)} {terms} .{tag}')
            payloads, raw_total = [], 0
            for at, header, payload, body in original_frames(wire, (group, 0)):
                _, stored, size, flag = parts(header, body)
                decoded = decode(codec, stored, size) if flag and codec != 0 else stored
                assert len(decoded) == size
                raw_total += payload - at + header[2][1]
                payloads.append(f'⟨{len(body)}, {header[2][1]}, {list(decoded)}⟩')
                raw_v2 += header[1][1] == 3 and not flag
            limits = ""
            if label == "gzip_raw_bypass" and group == 1:
                limits = f" {GZIP_ZERO}"
            if label == "zstd_raw_bypass" and group == 1:
                limits = f" {ZSTD_ZERO}"
            code.append(f'  checkPayloads (← load folder "{label}") {group} {BASE["lst"](payloads)} '
                        f'{hi - lo} {raw_total} .{tag} {codec}{limits}')
            total += len(pages)
        fields, batches = IPC["observation"](wire, width)
        code.append(f'  checkFile folder "{label}" (← load folder "{label}") {fields} {batches}')

    for test in controls:
        frames = original_frames(files[test.file], (test.group, 0))
        at, *_ = frames[test.ordinal]
        _, _, _, _, pages = observed[test.reference][test.group]
        before = BASE["state_term"](pages[test.ordinal][0][4])
        address = f"⟨{test.group}, 0, {json.dumps(PATH)}⟩"
        if test.version == 2:
            cause = f".v2 ({test.cause})"
        elif test.cause.startswith(".checksum"):
            cause = test.cause
        else:
            cause = f".v1Payload ({test.cause})"
        error = f".page {address} {test.ordinal} {at} {before} ({cause})"
        code.append(f'  refuse (← load folder "{test.file}") {test.group} {test.limits} ({error})')
        if test.readback:
            fields, batches = IPC["observation"](files[test.reference], 32, prefix=test.group)
            code.append(f'  sourceFailure (← load folder "{test.file}") {fields} {batches} '
                        f'(.group {test.group} (.chunk ({error})))')

    address = f"⟨1, 0, {json.dumps(PATH)}⟩"
    base = files["gzip_v2_32"]
    lo, hi = BASE["chunk_span"](base, (1, 0))
    raw_total = THRIFT["column_metadata"](MIXED["metadata"](base), 1, 0)[6][1]
    code.extend([
        f'  refuse (← load folder "gzip_raw_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi}⟩ '
        f'(.uncompressedSize {raw_total + 1} {raw_total}))',
        f'  refuse (← load folder "gzip_stored_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi - 1}⟩ (.framing .payloadBounds))',
        f'  refuseBinding (← load folder "legacy_lz4") (.column ⟨0, 0, {json.dumps(PATH)}⟩ (.codec 5))',
    ])
    V2["run_lean"](scratch, "TwoListMoreCodecs.lean", code)
    emitted = BASE["readback"](scratch, {key: (SAMPLES, width, rows) for key, (width, rows, _) in positives.items()})
    equivalents = [(f"{name}_raw_bypass", f"{name}_v2_32") for name in PRODUCERS]
    equivalents.append(("zstd_checksums", "mixed_groups"))
    for label, source in equivalents:
        for selection in ("field", "empty"):
            assert emitted[f"{label}_{selection}"] == emitted[f"{source}_{selection}"]

    print(f"Checked {total} original frames, {raw_v2} raw V2 suffixes, {len(emitted)} IPC streams through exact EOS "
          f"and {len(controls) + 3} typed refusals")
    return {group: BASE["fingerprints"](fixtures)
            for group, fixtures in (("genuine", genuine), ("authored", edited), ("lean_ipc", emitted))}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, fixtures in captured.items():
        assert fixtures == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
