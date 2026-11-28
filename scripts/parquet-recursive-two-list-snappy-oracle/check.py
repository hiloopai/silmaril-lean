"""Check original Snappy blocks and native two-LIST IPC independently."""

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
BASE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-v2-oracle/check.py"))
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-snappy-oracle/check.py"))
V2, THRIFT, MIXED, FRAMES, SCHEMA, PATH, GROUP, IPC = (
    BASE[key] for key in ("V2", "THRIFT", "MIXED", "FRAMES", "SCHEMA", "PATH", "GROUP", "IPC")
)
raw_chunks, header_body, encode, repack, expand, compress, frame_bytes, raw_bypass = (
    SNAPPY[key] for key in ("raw_chunks", "header_body", "encode", "repack", "snappy", "snappy_encode",
                            "frame_bytes", "raw_bypass")
)

LEAN = BASE["LEAN"] + """
open RecursiveSchema.Repeated.Chunk (bytesAt readV1Body readV2SuffixWith)
open RecursiveSchema.Repeated.Chunk (storedChunkBytes rawChunkBytes)

private structure PayloadTrace where
  storedSize : Nat
  decodedSize : Nat
  decoded : List UInt8

private def checkPayloads (file : Bytes) (group : Nat) (original : List PayloadTrace)
    (storedTotal decodedTotal : Nat) (limits : Limits := {}) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (Chunk.bind source.schema group)
  let seen ← take (read limits binding)
  let frames := seen.pages.map ObservedPage.frame
  unless binding.codec = .snappy ∧ binding.column.metadata.codec = 1 ∧
      storedChunkBytes frames = storedTotal ∧ rawChunkBytes frames = decodedTotal ∧
      frames.length = original.length do
    throw (IO.userError "original codec, page count or footer totals differ")
  for (frame, expected) in frames.zip original do
    let decoded ← match frame.value.kind with
      | .dataV1 _ => take (readV1Body limits.payload binding.codec.column file frame)
      | .dataV2 info => do
        let some spans := frame.v2Spans | throw (IO.userError "invalid original spans")
        let signedExtent := (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth source.schema.plan.kind
        take (readV2SuffixWith limits.payload binding.codec.column frame info (bytesAt file spans.values)
          (some signedExtent))
      | _ => throw (IO.userError "expected an original data frame")
    unless frame.value.compressedSize = expected.storedSize ∧ frame.value.uncompressedSize = expected.decodedSize ∧
        decoded.toList = expected.decoded do
      throw (IO.userError "decoded extent or original expanded bytes differ")
"""

SAMPLES = (True, True, True)
I32, I64 = TType.I32, TType.I64


def level_bytes(header):
    if header[1][1] == 0:
        return 0
    info = header[8][1]
    return info[5][1] + info[6][1]


def compress_identity(header, body):
    prefix = level_bytes(header)
    if header[1][1] == 3:
        header[8][1][7] = TType.BOOL, True
    return encode(header, body[:prefix] + compress(body[prefix:]), len(body))


def compress_file(wire):
    chunks = raw_chunks(wire)
    output = {
        key: [compress_identity(*header_body(page)) for page in pages] for key, pages in chunks.items()
    }
    footer = MIXED["metadata"](wire)
    for key in chunks:
        THRIFT["column_metadata"](footer, *key)[4] = I32, 1
    return repack(wire, output, footer)


def original_frames(wire, key=GROUP):
    return list(FRAMES(wire, *BASE["chunk_span"](wire, key)))


def fixtures():
    genuine, authored, positives, controls, caps = {}, {}, {}, [], []
    for width in (32, 64):
        for nullable in (SAMPLES, (False, False, False)):
            groups = BASE["samples"](nullable, width)
            # Keep null and empty states and ensure both widths produce genuine
            # compressed V2 suffixes, including in late-group tests.
            groups[1][-1][0].extend([17] * 96)
            schema = BASE["schema_for"](nullable, width)
            for page_version in (1, 2):
                profile = "nullable" if nullable == SAMPLES else "required"
                label = f"v{page_version}_{width}_{profile}"
                genuine[label] = BASE["write"](schema, groups, compression="SNAPPY",
                                               data_page_version=f"{page_version}.0")
                positives[label] = nullable, width, groups

    identity, labeled, baseline, _ = BASE["fixtures"]()
    for name in ("mixed", "v2_starts_rep_2", "v1_after_v2_rep_2"):
        authored[name] = compress_file(labeled[name])
    # The reframe uses exactly the rows of the original V2 oracle fixture.
    positives["mixed"] = baseline["mixed"]
    nullable, width, rows = baseline["native_32_7"]
    genuine["mixed_original"] = BASE["write"](BASE["schema_for"](nullable, width), rows,
                                              compression="SNAPPY", data_page_version="1.0")
    positives["mixed_original"] = nullable, width, rows
    list(BASE["inspect"](identity["native_32_7"], nullable, width, rows))

    def insert(wire, ordinal, changed):
        chunks = raw_chunks(wire)
        chunks[GROUP][ordinal] = changed
        return repack(wire, chunks)

    controls.extend([
        ("v2_starts_rep_2", 2, (5, 2, 2), ".v2 (.v2RowBoundary 5 2)"),
        ("v1_after_v2_rep_2", 4, "mixed", ".level (.closedAncestor 11 2 .closed)"),
    ])
    frames = raw_chunks(labeled["mixed"])[GROUP]
    header, body = header_body(frames[1])
    assert body[5] == 1
    bad = body[:5] + b"\x03" + body[6:]
    authored["invalid_v1_rep"] = insert(authored["mixed"], 1, compress_identity(header, bad))
    controls.append(("invalid_v1_rep", 1, "mixed", ".level (.repetition 3 3)"))

    trace = BASE["expected_slots"](rows[1], nullable)[6:11]
    mark = (trace[0][0], 6, trace[0][2])
    defective = BASE["v2_frame"](frames[3], [mark, *trace[1:]])
    header, body = header_body(defective)
    authored["invalid_v2_def"] = insert(authored["mixed"], 3, compress_identity(header, body))
    controls.append(("invalid_v2_def", 3, "mixed", ".level (.definition 6 6 5)"))

    for page_version in (1, 2):
        label = f"v{page_version}_32_nullable"
        wire = genuine[label]
        frames = original_frames(wire)
        ordinal = next(index for index, (_, header, _, _) in enumerate(frames)
                       if header[2][1] > header[3][1] and index > 0)
        _, original, _, stored = frames[ordinal]
        assert page_version == 1 or original[8][1][7][1]
        expected_size, stored_size = original[2][1], original[3][1]
        prefix = level_bytes(original)
        raw = frame_bytes(original, stored)
        wrap = (lambda error: f".v1Payload (.payload {error})") if page_version == 1 else (
            lambda error: f".v2 (.payload {error})"
        )

        def mutate(name, body, raw_extent, cause, *, crc=True):
            key = f"{name}_v{page_version}"
            header, _ = header_body(raw_chunks(wire)[GROUP][ordinal])
            authored[key] = insert(wire, ordinal, encode(header, body, raw_extent, crc=crc))
            controls.append((key, ordinal, label, cause))

        malformed = stored[:prefix] + b"\x80"
        stored_crc = original[4][1] & 0xffffffff
        mismatch = f"(.mismatch {stored_crc} {zlib.crc32(malformed)})"
        crc_cause = f".checksum {mismatch}" if page_version == 1 else f".v2 (.checksum {mismatch})"
        mutate("late_crc", malformed, expected_size, crc_cause, crc=False)
        mutate("late_malformed", malformed, expected_size, wrap("(.malformed .snappy)"))
        mutate("trailing", stored + b"\0", expected_size, wrap("(.trailingInput .snappy)"))
        mutate("block_extent", stored[:prefix] + compress(raw + b"\0"), expected_size, wrap(".outputSizeMismatch"))
        if page_version == 1:
            mutate("signed_tail", compress(raw + b"\0"), expected_size + 1, ".plain .trailingBytes")
        else:
            mutate("signed_extent", stored, expected_size + 1,
                   f".v2 (.v2SignedExtent {len(raw) + 1} {len(raw)})")
            key = "raw_bypass"
            bypass = raw_bypass(original, stored)
            authored[key] = insert(wire, ordinal, bypass)
            positives[key] = positives[label]
            header, raw_body = header_body(bypass)
            authored["raw_suffix"] = insert(wire, ordinal, encode(header, raw_body + b"\0", len(raw_body) + 1))
            controls.append(("raw_suffix", ordinal, label, ".plain .trailingBytes"))

        prior = frames[:ordinal]
        assert all(max(header[2][1], header[3][1]) < stored_size for _, header, _, _ in prior)
        checksum = ".checksum .byteLimit" if page_version == 1 else ".v2 (.checksum .byteLimit)"
        caps.extend([(label, ordinal, stored_size - 1, checksum), (label, ordinal, stored_size, wrap(".outputLimit"))])

    original = genuine["v2_32_nullable"]
    for label, field, delta in (("raw_total", 6, 1), ("stored_total", 7, -1)):
        footer = MIXED["metadata"](original)
        metadata = THRIFT["column_metadata"](footer, *GROUP)
        metadata[field] = I64, metadata[field][1] + delta
        authored[label] = SCHEMA["pack"](original, footer)
    return genuine, authored, positives, controls, caps


def verify(scratch):
    genuine, authored, positives, controls, caps = fixtures()
    files = genuine | authored
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    code = [LEAN, *BASE["V1"]["ENTRY"]]
    observed, total, raw_pages = {}, 0, 0
    for label, (nullable, width, groups) in positives.items():
        wire = files[label]
        observed[label] = list(BASE["inspect"](wire, nullable, width, groups, codec=1, expand=expand))
        for group, lo, hi, end, pages in observed[label]:
            opts = BASE["lst"](str(value).lower() for value in nullable)
            outer, inner, max_def = BASE["thresholds"](nullable)
            terms = BASE["lst"](BASE["checked_page_term"](page, nullable, width) for page in pages)
            code.append(f'  checkChunk (← load folder "{label}") {group} {opts} ({outer}, {inner}, {max_def}) '
                        f'.int{width} ⟨{lo}, {hi}⟩ {BASE["state_term"](end)} {terms} .snappy')
            frames = original_frames(wire, (group, 0))
            raw_total, payloads = 0, []
            for at, header, payload, stored in frames:
                raw_size, stored_size = header[2][1], header[3][1]
                raw_total += payload - at + raw_size
                decoded = frame_bytes(header, stored)
                payloads.append(f'⟨{stored_size}, {raw_size}, {list(decoded)}⟩')
            limits = ""
            if label == "raw_bypass" and group == GROUP[0]:
                assert all(not page[1][-1] for page in pages)
                maximum = max(header[3][1] for _, header, _, _ in frames)
                limits = f" {{ maxBodyBytes := {maximum} }}"
            code.append(f'  checkPayloads (← load folder "{label}") {group} {BASE["lst"](payloads)} '
                        f'{hi - lo} {raw_total}{limits}')
            total += len(pages)
            raw_pages += sum(page[1] is not None and not page[1][-1] for page in pages)
            if label == "mixed" and group == GROUP[0]:
                assert [page[0][-1][0][0] for page in pages] == [0, 1, 2, 0, 0]
                assert [page[1] is not None for page in pages] == [False, False, False, True, False]
            if label.startswith("v2_") and group == GROUP[0]:
                assert any(page[1][-1] for page in pages)
        fields, batches = IPC["observation"](wire, width)
        code.append(f'  checkFile folder "{label}" (← load folder "{label}") {fields} {batches}')

    address = f"⟨1, 0, {json.dumps(PATH)}⟩"

    def refuse_page(label, ordinal, reference, cause, limits="{}"):
        if isinstance(reference, str):
            _, _, _, _, pages = observed[reference][GROUP[0]]
            before = pages[ordinal][0][4]
        else:
            before = reference
        at, *_ = original_frames(files[label])[ordinal]
        error = f'.page {address} {ordinal} {at} {BASE["state_term"](before)} ({cause})'
        code.append(f'  refuse (← load folder "{label}") 1 {limits} ({error})')
        return error

    for label, ordinal, reference, cause in controls:
        original = refuse_page(label, ordinal, reference, cause)
        if label.startswith("late"):
            fields, batches = IPC["observation"](files[reference], 32, prefix=1)
            code.append(f'  sourceFailure (← load folder "{label}") {fields} {batches} '
                        f'(.group 1 (.chunk ({original})))')
    for label, ordinal, maximum, cause in caps:
        refuse_page(label, ordinal, label, cause, f"{{ maxBodyBytes := {maximum} }}")

    lo, hi = BASE["chunk_span"](files["v2_32_nullable"], GROUP)
    raw_total = next(meta[6][1] for key, meta, _, _ in V2["columns"](files["v2_32_nullable"]) if key == GROUP)
    code.extend([
        f'  refuse (← load folder "raw_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi}⟩ '
        f'(.uncompressedSize {raw_total + 1} {raw_total}))',
        f'  refuse (← load folder "stored_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi - 1}⟩ '
        f'(.framing .payloadBounds))',
    ])
    V2["run_lean"](scratch, "TwoListSnappy.lean", code)
    emitted = BASE["readback"](scratch, positives)
    for label, source in (("mixed", "mixed_original"), ("raw_bypass", "v2_32_nullable")):
        for selection in ("field", "empty"):
            assert emitted[f"{label}_{selection}"] == emitted[f"{source}_{selection}"]
    print(f"Checked {total} original frames, {raw_pages} raw V2 suffixes, "
          f"{len(emitted)} native IPC streams through exact EOS and {len(controls) + len(caps) + 2} typed refusals")
    return {group: BASE["fingerprints"](fixtures)
            for group, fixtures in (("genuine", genuine), ("authored", authored), ("lean_ipc", emitted))}


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
