"""Inspect original LZ4_RAW, GZIP and Zstandard LIST-path pages independently."""

from copy import deepcopy
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
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-snappy-oracle/check.py"))
REFERENCE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-more-codecs-oracle/check.py"))
V1, V2, FRAMES, write, fingerprints, EVENTS, GROUP = (
    SNAPPY[key] for key in ("V1", "V2", "FRAMES", "write", "fingerprints", "EVENTS", "GROUP")
)
schema_for, samples, chunk, triple, metadata, inspect_ipc, source_commands = (
    SNAPPY[key] for key in ("schema_for", "samples", "chunk", "triple", "metadata", "inspect_ipc", "source_commands")
)
raw_chunks, header_body, encode, repack, raw_bypass, original_frames = (
    SNAPPY[key] for key in ("raw_chunks", "header_body", "encode", "repack", "raw_bypass", "original_frames")
)
PRODUCERS, parts, GZIP_ZERO, ZSTD_ZERO, ZSTD_FRAME = (
    REFERENCE[key] for key in ("PRODUCERS", "parts", "GZIP_ZERO", "ZSTD_ZERO", "ZSTD_FRAME")
)


@dataclass(frozen=True)
class Refusal:
    fixture: str
    reference: str
    version: int
    cause: str
    group: int = 1
    ordinal: int = 0
    limits: str = "{}"
    late: bool = False


def native_cases():
    for width in (32, 64):
        for depth in (3, 6):
            nullable = (True,) * (depth + 1) if depth == 3 else tuple(
                i % 2 == (width == 32) for i in range(depth + 1))
            schema, rows = schema_for(nullable, width), samples(nullable, width)
            leaf = rows[1][0] = deepcopy(rows[1][0])
            for _ in range(depth - 1):
                leaf = leaf[-1]
            leaf.extend([17] * 120)
            for name, (codec, producer) in PRODUCERS.items():
                for page in (1, 2):
                    label = f"{name}_v{page}_{width}_depth_{depth}"
                    wire = write(schema, rows, compression=producer, data_page_version=f"{page}.0",
                                 max_rows_per_page=1, write_page_checksum=depth == 3)
                    yield label, wire, (schema, nullable, width, rows), [codec, codec]


def target(name, page):
    return f"{name}_v{page}_32_depth_3"


def fixtures(lz4, zstd, decode):
    genuine, authored, positives, refusals = {}, {}, {}, []
    for label, wire, case, codecs in native_cases():
        genuine[label] = wire
        positives[label] = case, codecs
    case, _ = positives[target("gzip", 2)]
    schema, nullable, width, rows = case
    for label, producer, group in (("identity_origin", "NONE", rows[0]), ("snappy_origin", "SNAPPY", rows[0][:2])):
        genuine[label] = write(schema, [group], compression=producer)
    origins = [("identity_origin", 0), (target("lz4", 1), 1), ("snappy_origin", 0),
               (target("gzip", 2), 1), (target("zstd", 2), 1)]
    authored["mixed_groups"] = REFERENCE["combine_groups"]([(genuine[label], ordinal) for label, ordinal in origins])
    positives["mixed_groups"] = (schema, nullable, width, [rows[0], rows[1], rows[0][:2], rows[1], rows[1]]), [0, 7, 1, 2, 6]

    def patch(label, source, edit, *, group=1, ordinal=0):
        wire = (genuine | authored)[source]
        chunks = raw_chunks(wire)
        frames = chunks[group, 0]
        frames[ordinal] = edit(*header_body(frames[ordinal]))
        authored[label] = repack(wire, chunks)

    def edit_payload(label, source, change, *, group=1, ordinal=0, crc=True):
        def edit(header, body):
            levels, stored, extent, flag = parts(header, body)
            assert flag
            return encode(header, levels + change(stored, extent), header[2][1], crc=crc)
        patch(label, source, edit, group=group, ordinal=ordinal)

    for name, (codec, _) in PRODUCERS.items():
        for page in (1, 2):
            source = target(name, page)
            _, header, _, body = original_frames(genuine[source])[0]
            raw_size, stored_size = header[2][1], len(body)
            assert stored_size < raw_size and parts(header, body)[-1]
            output = ".zstd (.scalar (.payload .outputLimit))" if name == "zstd" and page == 1 else ".payload .outputLimit"
            refusals.append(Refusal(source, source, page, ".checksum .byteLimit",
                                    limits=f"{{ maxBodyBytes := {stored_size - 1} }}"))
            refusals.append(Refusal(source, source, page, output, limits=f"{{ maxBodyBytes := {stored_size} }}"))
            label = f"{name}_v{page}_stored_crc"
            edit_payload(label, source, lambda stored, size: b"\0", crc=False)
            _, altered, _, edited_body = original_frames(authored[label])[0]
            crc = f".checksum (.mismatch {altered[4][1] & 0xffffffff} {zlib.crc32(edited_body)})"
            refusals.append(Refusal(label, source, page, crc))

        source = target(name, 2)
        label = f"{name}_raw_bypass"
        chunks = raw_chunks(genuine[source])
        changed = []
        for frame in chunks[GROUP]:
            header, body = header_body(frame)
            _, values, _, flag = parts(header, body)
            changed.append(raw_bypass(header, body, decode=lambda block, size: decode(codec, block, size))
                           if flag else frame)
            assert values or not flag
        authored[label] = repack(genuine[source], chunks | {GROUP: changed})
        positives[label] = positives[source]
        assert all(not parts(header, body)[3] for _, header, _, body in original_frames(authored[label]))

    def lz4_tail(stored, extent):
        changed = stored + b"\0"
        assert REFERENCE["LZ4"]["reference_decode"](lz4, changed, extent) is None
        return changed

    source = target("lz4", 2)
    edit_payload("late_lz4_tail", source, lz4_tail)
    refusals.append(Refusal("late_lz4_tail", source, 2, ".payload (.malformed .lz4Raw)", late=True))
    source = target("lz4", 1)
    patch("lz4_extent", source, lambda header, body: encode(header, body, header[2][1] + 1))
    refusals.append(Refusal("lz4_extent", source, 1, ".payload .outputSizeMismatch"))
    footer = metadata(genuine[source])
    REFERENCE["THRIFT"]["column_metadata"](footer, 0, 0)[4] = TType.I32, 5
    authored["legacy_lz4"] = REFERENCE["SCHEMA"]["pack"](genuine[source], footer)

    def gzip_trailer(member, size):
        corrupted = member[:-8] + bytes([member[-8] ^ 1]) + member[-7:]
        try:
            REFERENCE["GZIP"]["first_member"](corrupted, size)
        except zlib.error:
            return corrupted
        raise AssertionError("zlib accepted the corrupted member CRC")

    def gzip_extra(member, size, extra):
        assert REFERENCE["GZIP"]["first_member"](member + extra, size)[1] == extra
        return member + extra

    source = target("gzip", 1)
    edit_payload("late_gzip_trailer", source, gzip_trailer, ordinal=1)
    refusals.append(Refusal("late_gzip_trailer", source, 1, ".payload (.malformed .gzip)", ordinal=1, late=True))
    source = target("gzip", 2)
    for label, extra in (("gzip_trailing", b"\0"), ("gzip_second_member", zlib.compress(b"", wbits=31))):
        edit_payload(label, source, lambda stored, size: gzip_extra(stored, size, extra))
        refusals.append(Refusal(label, source, 2, ".payload (.trailingInput .gzip)"))
    refusals.append(Refusal(source, source, 2, ".payload .gzipIncomplete", limits=GZIP_ZERO))

    zstd_oracle = REFERENCE["ZSTD"]

    def checksummed(frame, size):
        raw = decode(6, frame, size)
        checked = zstd_oracle["ZSTD"]["run"](zstd, "compress-checksum", data=raw)
        assert zstd_oracle["frame_info"](zstd, checked)[5] == 1 and decode(6, checked, size) == raw
        return checked

    edit_payload("zstd_checksums", "mixed_groups", checksummed, group=4)
    positives["zstd_checksums"] = positives["mixed_groups"]

    def corrupt_checksum(frame, size):
        assert len(decode(6, frame, size)) == size
        changed = frame[:-1] + bytes([frame[-1] ^ 1])
        checked = subprocess.run([zstd, "decode", str(size)], input=changed, capture_output=True, check=False)
        assert checked.returncode == 3
        return changed

    edit_payload("late_zstd_checksum", "zstd_checksums", corrupt_checksum, group=4)
    refusals.append(Refusal("late_zstd_checksum", "zstd_checksums", 2, ZSTD_FRAME.format(".checksumMismatch"),
                            group=4, late=True))

    def zstd_extra(frame, _):
        changed = frame + frame
        assert zstd_oracle["frame_info"](zstd, changed)[0] == len(frame) < len(changed)
        return changed

    def zstd_dictionary(frame, _):
        descriptor = frame[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = frame[:4] + bytes([descriptor | 1]) + frame[5:at] + b"\x07" + frame[at:]
        assert zstd_oracle["frame_info"](zstd, changed)[4] == 7
        return changed

    source = target("zstd", 2)
    for label, change, cause in (
        ("zstd_second_frame", zstd_extra, ".trailingInput"),
        ("zstd_dictionary", zstd_dictionary, "(.unsupportedDictionary 7)"),
    ):
        edit_payload(label, source, change)
        refusals.append(Refusal(label, source, 2, ZSTD_FRAME.format(cause)))
    refusals.extend([
        Refusal(source, source, 2, ZSTD_FRAME.format(".windowLimit"), limits=ZSTD_ZERO),
        Refusal(source, source, 2, ".zstd (.frame (.compressed (.block (.tables (.prefix .sequenceLimit)))))",
                limits="{ zstd := { ({} : Chunk.Limits).zstd with commandsPerBlock := 0 } }"),
    ])

    source = target("gzip", 2)
    for label, field, delta in (("raw_total", 6, 1), ("stored_total", 7, -1)):
        wire = genuine[source]
        footer = metadata(wire)
        column = REFERENCE["THRIFT"]["column_metadata"](footer, *GROUP)
        column[field] = TType.I64, column[field][1] + delta
        authored[label] = REFERENCE["SCHEMA"]["pack"](wire, footer)
    return genuine, authored, positives, refusals


def address(group):
    return f'⟨{group}, 0, {json.dumps(["chain"] + ["list", "element"] * 3)}⟩'


def verify(folder):
    lz4, zstd, decode = REFERENCE["reference_codecs"](folder)
    genuine, authored, positives, refusals = fixtures(lz4, zstd, decode)
    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code, entry = [SNAPPY["LEAN"]], [*V1["ENTRY"]]
    count, bypasses, observations = 0, 0, {}
    caps = {"gzip_raw_bypass": {1: GZIP_ZERO}, "zstd_raw_bypass": {1: ZSTD_ZERO}}
    for label, (case, codecs) in positives.items():
        observations[label], commands = source_commands(label, files[label], case, codecs, decode, caps.get(label))
        for lo, hi, _, pages in observations[label]:
            count += len(pages)
            if "_depth_" in label:
                assert len(pages) >= 2
            for _, header, _, body in FRAMES(files[label], lo, hi):
                bypasses += int(header[1][1] == 3 and not parts(header, body)[3])
        code.extend(commands)
        entry.append(f"  verify_{label} folder")

    code.append("private def controls (folder : System.FilePath) : IO Unit := do")
    entry.append("  controls folder")
    for test in refusals:
        at, *_ = original_frames(files[test.fixture], (test.group, 0))[test.ordinal]
        before = triple(observations[test.reference][test.group][-1][test.ordinal][-3])
        if test.version == 2:
            cause = f".v2 ({test.cause})"
        elif test.cause.startswith(".checksum"):
            cause = test.cause
        else:
            cause = f".v1Payload ({test.cause})"
        error = f".page {address(test.group)} {test.ordinal} {at} {before} ({cause})"
        code.append(f'  refuse (← load folder "{test.fixture}") {test.group} {test.limits} ({error})')
        if test.late:
            (schema, _, width, groups), _ = positives[test.reference]
            code.append(f'  sourceFailure (← load folder "{test.fixture}") {EVENTS["declarations"](schema)} '
                        f'{EVENTS["batch_terms"](groups[:test.group], width)} (.group {test.group} (.chunk ({error})))')

    source = files[target("gzip", 2)]
    lo, hi = chunk(source)
    raw_total = REFERENCE["THRIFT"]["column_metadata"](metadata(source), *GROUP)[6][1]
    code.extend([
        f'  refuse (← load folder "raw_total") 1 {{}} (.chunk {address(1)} ⟨{lo}, {hi}⟩ '
        f'(.rawSize {raw_total + 1} {raw_total}))',
        f'  refuse (← load folder "stored_total") 1 {{}} (.chunk {address(1)} ⟨{lo}, {hi - 1}⟩ '
        '(.framing .payloadBounds))',
        f'  refuseBinding (← load folder "legacy_lz4") (.column {address(0)} (.codec 5))',
    ])
    V2["run_lean"](folder, "ListPathCodecs.lean", code + entry)

    emitted = {}
    for label, ((schema, _, _, groups), _) in positives.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = emitted[name] = (folder / f"{name}.arrow").read_bytes()
            inspect_ipc(wire, schema, groups, selection)
    for selection in ("field", "empty"):
        for name in PRODUCERS:
            assert emitted[f"{name}_raw_bypass_{selection}"] == emitted[f"{target(name, 2)}_{selection}"]
        assert emitted[f"zstd_checksums_{selection}"] == emitted[f"mixed_groups_{selection}"]
    print(f"Checked {len(positives)} inputs, {count} original frames, {bypasses} raw V2 suffixes, "
          f"{len(emitted)} native IPC streams and {len(refusals) + 3} typed controls")
    return {
        "reference": {
            "liblz4": REFERENCE["LZ4"]["PIN"],
            "libzstd": REFERENCE["ZSTD"]["ZSTD"]["PIN"],
            "zlib": zlib.ZLIB_RUNTIME_VERSION,
        },
        "genuine_parquet": fingerprints(genuine),
        "authored_parquet": fingerprints(authored),
        "lean_ipc": fingerprints(emitted),
    }


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, expected in captured.items():
        assert expected == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
