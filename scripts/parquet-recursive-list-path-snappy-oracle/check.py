"""Check original Snappy V1 and V2 LIST-path frames and native IPC."""

from copy import deepcopy
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
BASE = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-v2-oracle/check.py"))
TWO_SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-snappy-oracle/check.py"))
NATIVE, EVENTS, TWO, GROUP = (BASE[key] for key in ("NATIVE", "EVENTS", "TWO", "GROUP"))
V1, V2, FRAMES, lst, write, fingerprints = (BASE[key] for key in ("V1", "V2", "FRAMES", "lst", "write", "fingerprints"))
capture, chunk, schema_for, samples, page_term, triple, metadata, inspect_ipc = (
    BASE[key] for key in ("capture", "chunk", "schema_for", "samples", "page_term", "triple", "metadata", "inspect_ipc")
)
SNAPPY = TWO_SNAPPY["SNAPPY"]
expand, compress, encode, repack, raw_bypass, frame_bytes, raw_chunks, header_body = (
    SNAPPY[key] for key in ("snappy_block", "snappy_encode", "encode", "repack", "raw_bypass",
                            "frame_bytes", "raw_chunks", "header_body")
)
compress_file, level_bytes = TWO_SNAPPY["compress_file"], TWO_SNAPPY["level_bytes"]


LEAN = BASE["LEAN"] + """
open RecursiveSchema.Repeated.Chunk (readV1Body readV2SuffixWith bytesAt storedChunkBytes rawChunkBytes)

set_option maxRecDepth 32768

private def checkPayloads (file : Bytes) (depth group : Nat) (codec : Chunk.Codec)
    (storedSize rawSize : Nat) (expanded : List KBytes) (limits : Chunk.Limits := {}) : IO Unit := do
  let source ← take (openFile { maxSchemaDepth := 2 * depth + 2 } file)
  let binding ← take (Chunk.bind source.schema group)
  let seen ← take (Chunk.read limits binding)
  let frames := seen.frames
  unless binding.codec = codec && binding.column.metadata.codec = codec.column.id &&
      storedChunkBytes frames = storedSize && rawChunkBytes frames = rawSize && frames.length = expanded.length do
    throw (IO.userError "original codec, frame count or column totals differ")
  for (frame, expected) in frames.zip expanded do
    let actual ← match frame.value.kind with
      | .dataV1 _ => take (readV1Body limits.payload codec.column file frame)
      | .dataV2 info => do
        let some spans := frame.v2Spans | throw (IO.userError "invalid original spans")
        let width := RecursiveSchema.Chunk.wordWidth source.schema.plan.shape.leaf.2
        let extent := (info.numValues - info.numNulls) * width
        take (readV2SuffixWith limits.payload codec.column frame info (bytesAt file spans.values) (some extent))
      | _ => throw (IO.userError "expected original data frame")
    unless actual.toList == expected.toList do throw (IO.userError "original decoded payload bytes differ")
"""


def original_frames(wire, key=GROUP):
    return list(FRAMES(wire, *chunk(wire, key)))


def fixtures():
    genuine, authored, positives, controls = {}, {}, {}, []

    for width in (32, 64):
        for depth in (3, 4, 6, 16):
            if depth == 3:
                nullable = (True,) * (depth + 1)
            elif depth == 4:
                nullable = (False,) * (depth + 1)
            else:
                nullable = tuple(i % 2 == (width == 32) for i in range(depth + 1))
            schema, groups = schema_for(nullable, width), samples(nullable, width)
            long_row = groups[1][0] = deepcopy(groups[1][0])
            leaf_values = long_row
            for _ in range(depth - 1):
                leaf_values = leaf_values[-1]
            leaf_values.extend([17] * 120)
            for version in (1, 2):
                label = f"native_v{version}_{width}_depth_{depth}"
                genuine[label] = write(schema, groups, compression="SNAPPY", data_page_version=f"{version}.0",
                                       max_rows_per_page=1, write_page_checksum=depth != 6)
                positives[label] = (schema, nullable, width, groups), [1] * len(groups)

    _, base_cases, base_edits, _, base_errors = BASE["fixtures"]()
    authored["mixed"] = compress_file(base_edits["mixed"])
    positives["mixed"] = base_cases["mixed"], [1, 1]
    schema, _, _, groups = base_cases["mixed"]
    genuine["mixed_original"] = write(schema, groups, compression="SNAPPY", data_page_version="2.0")
    positives["mixed_original"] = base_cases["mixed"], [1, 1]

    # Keep the original second group with its authored compressed page segments.
    identity = base_edits["mixed"]
    footer = metadata(identity)
    TWO["THRIFT"]["column_metadata"](footer, *GROUP)[4] = TType.I32, 1
    authored["mixed_codec_groups"] = repack(identity, raw_chunks(identity) | {
        GROUP: raw_chunks(authored["mixed"])[GROUP]
    }, footer)
    positives["mixed_codec_groups"] = base_cases["mixed"], [0, 1]

    def address(depth):
        return f'⟨1, 0, {json.dumps(["chain"] + ["list", "element"] * depth)}⟩'

    def page_control(label, wire, ordinal, start, cause, *, caps="{}", depth=3):
        at = original_frames(wire)[ordinal][0]
        controls.append((label, caps, f".page {address(depth)} {ordinal} {at} {triple(start)} ({cause})"))

    mixed = capture(authored["mixed"], *base_cases["mixed"], codecs=[1, 1], expand=expand)[1][-1]
    for label, ordinal in (("v2_starts_inside_3", 3), ("v1_continues_v2_3", 5)):
        original_error = dict(base_errors)[label]
        cause = original_error.split("⟩ (", 2)[-1][:-1]
        assert cause.startswith((".v2 ", ".level "))
        authored[label] = compress_file(base_edits[label])
        page_control(label, authored[label], ordinal, mixed[ordinal][-3], cause)

    for version in (1, 2):
        label = f"native_v{version}_32_depth_3"
        wire = genuine[label]
        ordinal = 0
        _, original, _, stored = original_frames(wire)[ordinal]
        assert original[2][1] > original[3][1]
        assert version == 1 or original[8][1][7][1]
        chunks = raw_chunks(wire)
        template = chunks[GROUP][ordinal]
        prefix = level_bytes(original)
        expected_size, stored_size = original[2][1], original[3][1]
        raw = frame_bytes(original, stored)
        stage = ".v1Payload" if version == 1 else ".v2"
        checksum = ".checksum" if version == 1 else ".v2 (.checksum"
        close = ")" if version == 2 else ""

        def splice(frame):
            group = chunks[GROUP].copy()
            group[ordinal] = frame
            return repack(wire, chunks | {GROUP: group})

        def edit(name, body, extent, cause, *, crc=True):
            key = f"{name}_v{version}"
            header, _ = header_body(template)
            authored[key] = splice(encode(header, body, extent, crc=crc))
            page_control(key, authored[key], ordinal, (0, 0, 0), cause)

        malformed = stored[:prefix] + b"\x80"
        crc = original[4][1] & 0xffffffff
        edit("late_crc", malformed, expected_size,
             f"{checksum} (.mismatch {crc} {zlib.crc32(malformed)}){close}", crc=False)
        edit("late_malformed", malformed, expected_size, f"{stage} (.payload (.malformed .snappy))")
        edit("trailing", stored + b"\0", expected_size, f"{stage} (.payload (.trailingInput .snappy))")
        edit("block_extent", stored[:prefix] + compress(raw + b"\0"), expected_size,
             f"{stage} (.payload .outputSizeMismatch)")
        if version == 1:
            edit("signed_extent", compress(raw + b"\0"), expected_size + 1, ".plain .trailingBytes")
        else:
            edit("signed_extent", stored, expected_size + 1, f".v2 (.v2SignedExtent {len(raw) + 1} {len(raw)})")
            header, _ = header_body(template)
            bypass = raw_bypass(header, stored)
            authored["raw_fallback"] = splice(bypass)
            positives["raw_fallback"] = positives[label]
            header, raw_body = header_body(bypass)
            assert raw_body[prefix:] == raw and raw
            authored["raw_trailing"] = splice(encode(header, raw_body + b"\0", len(raw_body) + 1))
            page_control("raw_trailing", authored["raw_trailing"], ordinal, (0, 0, 0), ".plain .trailingBytes")

        page_control(label, wire, ordinal, (0, 0, 0), f"{checksum} .byteLimit{close}",
                     caps=f"{{ maxBodyBytes := {stored_size - 1} }}")
        page_control(label, wire, ordinal, (0, 0, 0), f"{stage} (.payload .outputLimit)",
                     caps=f"{{ maxBodyBytes := {stored_size} }}")

    original = genuine["native_v2_32_depth_3"]
    lo, hi = chunk(original)
    original_column = TWO["THRIFT"]["column_metadata"](metadata(original), *GROUP)
    for key, field, delta, stop, cause in (
        ("raw_total", 6, 1, hi, f"(.rawSize {original_column[6][1] + 1} {original_column[6][1]})"),
        ("stored_total", 7, -1, hi - 1, "(.framing .payloadBounds)"),
    ):
        footer = metadata(original)
        TWO["THRIFT"]["column_metadata"](footer, *GROUP)[field] = TType.I64, original_column[field][1] + delta
        authored[key] = TWO["SCHEMA"]["pack"](original, footer)
        controls.append((key, "{}", f".chunk {address(3)} ⟨{lo}, {stop}⟩ {cause}"))
    return genuine, authored, positives, controls


def bytes_term(payload):
    return f"(KBytes.leaf {len(payload)} {int.from_bytes(payload, 'little')})"


def source_commands(label, wire, case, codecs, decode, caps=None):
    schema, nullable, width, groups = case
    depth = len(nullable) - 1
    terms = NATIVE["CORE"]["ROWS"]
    layouts, payload_checks = [], []
    manifest = capture(wire, *case, codecs=codecs, expand=decode)
    tags = {0: "uncompressed", 1: "snappy", 2: "gzip", 6: "zstd", 7: "lz4Raw"}
    caps = {} if caps is None else caps
    for ordinal, ((lo, hi, stop, pages), rows, codec) in enumerate(zip(manifest, groups, codecs, strict=True)):
        original = list(FRAMES(wire, lo, hi))
        expected = lst(page_term(page, width, header, codec)
                       for page, (_, header, _, _) in zip(pages, original, strict=True))
        layouts.append(f"⟨{terms['batch_term'](rows, width)}, ⟨{lo}, {hi}⟩, {triple(stop)}, {expected}⟩")

        def value_bytes(header, body):
            if codec == 0:
                return body[level_bytes(header):]
            return frame_bytes(header, body, decode=lambda block, size: decode(codec, block, size))

        decoded = lst(bytes_term(value_bytes(header, body)) for _, header, _, body in original)
        stored = sum(body_at - at + header[3][1] for at, header, body_at, _ in original)
        raw = sum(body_at - at + header[2][1] for at, header, body_at, _ in original)
        cap = f" {caps[ordinal]}" if ordinal in caps else ""
        payload_checks.append(f'  checkPayloads (← load folder "{label}") {depth} {ordinal} .{tags[codec]} '
                              f'{stored} {raw} {decoded}{cap}')
    field = terms["field_term"](schema.field(0))
    return manifest, [
        f"private def verify_{label} (folder : System.FilePath) : IO Unit := do",
        f'  checkNative (← load folder "{label}") {depth} ⟨[{field}]⟩ {lst(layouts)}',
        *payload_checks,
        f'  checkIpc folder "{label}" (← load folder "{label}") {depth} '
        f'{EVENTS["declarations"](schema)} {EVENTS["batch_terms"](groups, width)}',
    ]


def verify(folder):
    genuine, authored, positives, controls = fixtures()
    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code, entry = [LEAN], [*V1["ENTRY"]]
    total_frames = genuine_raw = genuine_raw_with_words = 0
    for label, (case, codecs) in positives.items():
        wire = files[label]
        manifest, commands = source_commands(label, wire, case, codecs, expand)
        for ordinal, (lo, hi, _, pages) in enumerate(manifest):
            original = list(FRAMES(wire, lo, hi))
            if label.startswith("native_"):
                assert len(pages) >= 2
            if label.startswith("native_v2"):
                assert any(header[8][1][7][1] for _, header, _, _ in original) or ordinal == 0
                for _, header, _, body in original:
                    if not header[8][1][7][1]:
                        genuine_raw += 1
                        genuine_raw_with_words += len(body) > level_bytes(header)
            total_frames += len(pages)
        code.extend(commands)
        entry.append(f"  verify_{label} folder")

    code.append("private def controls (folder : System.FilePath) : IO Unit := do")
    entry.append("  controls folder")
    for label, cap, cause in controls:
        code.append(f'  refuse (← load folder "{label}") 1 {cap} ({cause})')
        if label.startswith("late_"):
            version = label[-1]
            (schema, _, width, groups), _ = positives[f"native_v{version}_32_depth_3"]
            code.append(f'  sourceFailure (← load folder "{label}") {EVENTS["declarations"](schema)} '
                        f'{EVENTS["batch_terms"](groups[:1], width)} (.group 1 (.chunk ({cause})))')
    V2["run_lean"](folder, "ListPathSnappy.lean", code + entry)

    emitted = {}
    for label, ((schema, _, _, groups), _) in positives.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = emitted[name] = (folder / f"{name}.arrow").read_bytes()
            inspect_ipc(wire, schema, groups, selection)
    for selection in ("field", "empty"):
        for label in ("mixed", "mixed_codec_groups"):
            assert emitted[f"{label}_{selection}"] == emitted[f"mixed_original_{selection}"]
        assert emitted[f"raw_fallback_{selection}"] == emitted[f"native_v2_32_depth_3_{selection}"]
    print(f"Checked {len(positives)} inputs, {total_frames} original frames, {genuine_raw} genuine raw V2 suffixes "
          f"({genuine_raw_with_words} with signed words), {len(emitted)} native IPC streams and {len(controls)} typed controls")
    return {kind: fingerprints(values) for kind, values in {
        "genuine_parquet": genuine, "authored_parquet": authored, "lean_ipc": emitted,
    }.items()}


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
