"""Check original TwoListStruct Snappy frames, child streams and projected IPC."""

from copy import deepcopy
import json
from pathlib import Path
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-v2-oracle/check.py"))
NATIVE, EVENTS, IPC = (BASE[key] for key in ("NATIVE", "EVENTS", "IPC"))
THRIFT, frames_in, lst, page_term, triple = (BASE[key] for key in
                                           ("THRIFT", "frames_in", "lst", "page_term", "triple"))
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-snappy-oracle/check.py"))
TAGS = {0: "uncompressed", 1: "snappy", 2: "gzip", 6: "zstd", 7: "lz4Raw"}
encode, expand, frame_bytes, header_body, level_bytes, raw_bypass, raw_chunks, repack = (
    SNAPPY[key] for key in ("encode", "expand", "frame_bytes", "header_body",
                           "level_bytes", "raw_bypass", "raw_chunks", "repack")
)


LEAN = BASE["LEAN"].replace("public def main", """
open RecursiveSchema.Repeated.Chunk (bytesAt readV1Body readV2SuffixWith storedChunkBytes rawChunkBytes)

private def checkPayloads (file : Bytes) (group : Nat) (side : Side) (codec : RecursiveSchema.ListPath.Chunk.Codec)
    (storedTotal rawTotal : Nat) (bytes : List (KBytes × KBytes)) (limits : Reader.Limits := {}) : IO Unit := do
  let source ← take (openFile {} file)
  let bound ← take (Reader.bindGroup source.snapshot group)
  let column ← take (Reader.bindColumn source.schema bound side)
  let observed ← take (Reader.readColumn limits column)
  unless column.codec = codec && column.column.metadata.codec = codec.column.id &&
      storedChunkBytes observed.frames = storedTotal && rawChunkBytes observed.frames = rawTotal &&
      observed.frames.length = bytes.length do
    throw (IO.userError "original column codec, page count or footer totals differ")
  for (frame, stored, plain) in observed.frames.zip bytes do
    let expanded ← match frame.value.kind with
      | .dataV1 _ | .dictionary _ => take (readV1Body limits.payload codec.column file frame)
      | .dataV2 info => do
        let some spans := frame.v2Spans | throw (IO.userError "invalid original V2 spans")
        let width := RecursiveSchema.Chunk.wordWidth (source.schema.plan.child side).2
        let extent := if info.encoding = 0 then some ((info.numValues - info.numNulls) * width) else none
        take (readV2SuffixWith limits.payload codec.column frame info (bytesAt file spans.values) extent)
      | .skipped _ => throw (IO.userError "unexpected skipped frame")
    unless (bytesAt file frame.payload).toList == stored.toList && expanded.toList == plain.toList do
      throw (IO.userError "original stored or decoded payload bytes differ")

private def checkFailure (input : Bytes) (limits : Reader.Limits) (completedPrefix : List Observation)
    (wanted : Reader.Events.Error) : IO Unit := do
  for selection in [Selection.field, .empty] do
    let ⟨_, trace⟩ ← take (Reader.Events.readProjected {} limits input selection)
    let selected := completedPrefix.map selection.batch
    unless trace.termination == .readError wanted && trace.batches.map eraseBatch == selected do
      throw (IO.userError "original Events failure or completed prefix differs")
    for budget in [({} : Arrow.RecursiveSchema.Batch.Limits), exhausted] do
      let .error (.readError actual completed) := convert {} limits budget input selection |
        throw (IO.userError "expected the original typed source failure")
      unless actual = wanted && completed == selected do
        throw (IO.userError "original IPC failure or completed prefix differs")

set_option maxHeartbeats 2000000 in
public def main""")


def native(flags, optional, version, *, reverse=False, **options):
    schema, groups, _ = NATIVE["native"](flags, struct_nullable=optional)
    if reverse:
        outer = schema.field(0)
        inner = outer.type.value_field
        element = inner.type.value_field
        element = element.with_type(pa.struct(list(reversed(list(element.type)))))
        schema = pa.schema([outer.with_type(pa.list_(inner.with_type(pa.list_(element))))])
    groups = deepcopy(groups)
    groups[1][0][0].extend([{"lo": -17, "hi": 2**40}] * 64)
    settings = dict(compression="snappy", data_page_version=f"{version}.0", max_rows_per_page=1,
                    write_batch_size=1)
    return schema, groups, NATIVE["write"](schema, groups, **(settings | options))


def column_codec(wire, key):
    return THRIFT["column_metadata"](NATIVE["metadata"](wire), *key)[4][1]


def decoded(header, stored, codec, decode_block):
    if codec != 0:
        return frame_bytes(header, stored, decode=lambda body, size: decode_block(codec, body, size))
    assert len(stored) == header[2][1]
    return stored[level_bytes(header):] if header[1][1] == 3 else stored


def fixtures():
    genuine, authored, errors = {}, {}, []
    for optional in (False, True):
        for version in (1, 2):
            shape = "optional" if optional else "required"
            for flags in ((True,) * 4, (False, False, False, True), (True, True, True, False)):
                tag = "".join(str(int(flag)) for flag in flags)
                genuine[f"{shape}_v{version}_{tag}"] = native(flags, optional, version, reverse=flags[2] != flags[3],
                                                               write_page_checksum=flags[0])
    all_flags = (True,) * 4
    path = ".".join(NATIVE["PATH"])
    genuine["per_child_v2"] = native(all_flags, True, 2,
                                     compression={f"{path}.lo": "snappy", f"{path}.hi": "NONE"})
    assert [column_codec(genuine["per_child_v2"][2], (0, side)) for side in (0, 1)] == [1, 0]

    _, base_authored, base_cases, _, _, _ = BASE["fixtures"]()
    schema, groups, baseline = base_cases["mixed_versions"]
    chunks = raw_chunks(baseline)
    footer = NATIVE["metadata"](baseline)
    for key, frames in chunks.items():
        if key[0] != key[1]:
            chunks[key] = [SNAPPY["compress_identity"](*header_body(frame)) for frame in frames]
            THRIFT["column_metadata"](footer, *key)[4] = TType.I32, 1
    mixed = authored["mixed_versions_and_codecs"] = repack(baseline, chunks, footer)
    assert [[column_codec(mixed, (group, side)) for side in (0, 1)] for group in (0, 1)] == [[0, 1], [1, 0]]
    positives = genuine | {"mixed_versions_and_codecs": (schema, groups, mixed),
                           "uncompressed_reference": (schema, groups, baseline)}
    authored["uncompressed_reference"] = base_authored["mixed_versions"]

    key = (1, 1)
    addr = NATIVE["address"](*key)
    for version in (1, 2):
        label = f"optional_v{version}_1111"
        schema, groups, wire = genuine[label]
        columns = raw_chunks(wire)
        frames = frames_in(wire, *key)
        ordinal, (_, header, _, stored) = next(
            (i, frame) for i, frame in enumerate(frames) if frame[1][2][1] > 512)
        assert ordinal == 0 and header[2][1] > header[3][1]
        level = level_bytes(header)
        if version == 2:
            assert header[8][1][7][1] and level > 0

        def splice(frame):
            return repack(wire, columns | {key: [*columns[key][:ordinal], frame, *columns[key][ordinal + 1:]]})

        def page_failure(label, changed, cause, limits="{}"):
            byte = frames_in(changed, *key)[ordinal][0]
            errors.append((label, limits, f".chunk (.page {addr} {ordinal} {byte} ⟨0, 0, 0⟩ ({cause}))"))

        stage = ".v1Payload" if version == 1 else ".v2"
        crc = header[4][1] & 0xffffffff
        malformed = stored[:level] + b"\x80"
        mismatch = f".mismatch {crc} {zlib.crc32(malformed)}"
        crc_error = f".checksum ({mismatch})"
        if version == 2:
            crc_error = f".v2 ({crc_error})"
        for fault, body, cause, refresh_crc in (
            ("crc", malformed, crc_error, False),
            ("malformed", malformed, f"{stage} (.payload (.malformed .snappy))", True),
            ("trailing", stored + b"\0", f"{stage} (.payload (.trailingInput .snappy))", True),
        ):
            name = f"late_{fault}_v{version}"
            changed = authored[name] = splice(encode(deepcopy(header), body, header[2][1], crc=refresh_crc))
            page_failure(name, changed, cause)

        name = f"late_declared_extent_v{version}"
        changed = authored[name] = splice(encode(deepcopy(header), stored, header[2][1] + 1))
        plain_extent = header[2][1] - level
        extent_error = (".v1Payload (.payload .outputSizeMismatch)" if version == 1 else
                        f".v2 (.v2SignedExtent {plain_extent + 1} {plain_extent})")
        page_failure(name, changed, extent_error)

        prior_max = max(max(h[2][1], len(b)) for col in ((0, 0), (0, 1), (1, 0))
                        for _, h, _, b in frames_in(wire, *col))
        limit = max(prior_max, len(stored))
        assert limit < header[2][1] - level
        page_failure(label, wire, f"{stage} (.payload .outputLimit)", f"{{ maxBodyBytes := {limit} }}")

        if version == 2:
            name = "v2_raw_bypass"
            bypass = authored[name] = splice(raw_bypass(deepcopy(header), stored))
            positives[name] = schema, groups, bypass
            assert len(frames_in(bypass, *key)[ordinal][3]) > limit
            page_failure(name, bypass, ".v2 (.checksum .byteLimit)", f"{{ maxBodyBytes := {limit} }}")

            column = THRIFT["column_metadata"](NATIVE["metadata"](wire), *key)
            lo, hi = next((lo, hi) for k, _, lo, hi in NATIVE["V2"]["columns"](wire) if k == key)
            for size_kind, field, adjustment, stop, cause in (
                ("raw", 6, 1, hi, f".rawSize {column[6][1] + 1} {column[6][1]}"),
                ("stored", 7, -1, hi - 1, ".framing .payloadBounds"),
            ):
                name = f"late_{size_kind}_total"
                changed_footer = NATIVE["metadata"](wire)
                THRIFT["column_metadata"](changed_footer, *key)[field] = TType.I64, column[field][1] + adjustment
                authored[name] = NATIVE["TWO"]["SCHEMA"]["pack"](wire, changed_footer)
                errors.append((name, "{}", f".chunk (.chunk {addr} ⟨{lo}, {stop}⟩ ({cause}))"))

    probes = {
        "other_codec": native(all_flags, True, 2, compression="gzip")[2],
        "dictionary": native(all_flags, True, 2, use_dictionary=True)[2],
    }
    return genuine, authored, positives, probes, errors


def bytes_term(data):
    return f"(KBytes.leaf {len(data)} {int.from_bytes(data, 'little')})"


def source_commands(label, schema, groups, wire, decode_block, *, checksums=True, limits="{}", dictionaries=None):
    commands = []
    counts = {"v1": 0, "v2": 0, "v2_raw_words": 0}
    ceiling, columns = NATIVE["inspect"](wire, schema, groups, versions=(0, 3),
                                         checksums=checksums, decode_block=decode_block, dictionaries=dictionaries)
    logical = EVENTS["pyarrow_groups"](wire, schema, groups)
    outer = schema.field(0)
    inner = outer.type.value_field
    element = inner.type.value_field
    for (group, side), ((lo, hi), pages) in columns.items():
        frames = frames_in(wire, group, side)
        width = element.type[side].type.bit_width
        codec = column_codec(wire, (group, side))
        tag = ".left" if side == 0 else ".right"
        path = [outer.name, "list", inner.name, "list", element.name, element.type[side].name]
        data_frames = (frame for frame in frames if frame[1][1][1] != 2)
        terms = lst(page_term(page, width, frame[1], codec) for page, frame in zip(pages, data_frames, strict=True))
        commands.append(f'  checkColumn (← load folder "{label}") {group} {tag} {NATIVE["path_term"](path)} '
                        f'{ceiling} ⟨{lo}, {hi}⟩ {terms}')
        pairs = []
        raw_total = 0
        for at, header, body_at, stored in frames:
            plain = decoded(header, stored, codec, decode_block)
            pairs.append(f"({bytes_term(stored)}, {bytes_term(plain)})")
            raw_total += body_at - at + header[2][1]
            if header[1][1] == 2:
                continue
            v2 = header[1][1] == 3
            counts["v2" if v2 else "v1"] += 1
            if v2 and codec != 0 and not header[8][1].get(7, (None, True))[1] and plain:
                counts["v2_raw_words"] += 1
        lean_codec = f".{TAGS[codec]}"
        commands.append(f'  checkPayloads (← load folder "{label}") {group} {tag} {lean_codec} '
                        f'{hi - lo} {raw_total} {lst(pairs)} {limits}')
    fields, batches = IPC["fields_term"](schema), IPC["batches_term"](schema, logical)
    commands.extend([f'  checkRows (← load folder "{label}") {batches}',
                     f'  checkDirect (← load folder "{label}") {fields} {batches}',
                     f'  checkIpc folder "{label}" {fields} {batches}'])
    return commands, logical, columns, counts


def decode_snappy(codec, data, size):
    assert codec == 1
    return expand(data, size)


def verify(folder):
    genuine, authored, positives, probes, errors = fixtures()
    originals = {label: case[2] for label, case in genuine.items()}
    for label, wire in (originals | authored | probes).items():
        (folder / f"{label}.parquet").write_bytes(wire)

    commands, expected = [LEAN], {}
    counts = {"v1": 0, "v2": 0, "v2_raw_words": 0}
    for label, (schema, groups, wire) in positives.items():
        case, logical, columns, frame_counts = source_commands(
            label, schema, groups, wire, decode_snappy, checksums=not label.endswith("_0001"))
        if label == "mixed_versions_and_codecs":
            pages = columns[1, 0][1]
            assert [page[-1][0][0] for page in pages[:3]] == [0, 2, 1]
            assert [frame[1][1][1] for frame in frames_in(wire, 1, 0)[:3]] == [0, 0, 0]
        expected[label] = schema, logical
        commands.extend(case)
        for kind, count in frame_counts.items():
            counts[kind] += count

    schema, first = expected["optional_v2_1111"]
    prefix = IPC["batches_term"](schema, first[:1])
    for label, limits, error in errors:
        commands.append(f'  groupRefusal (← load folder "{label}") 1 {limits} ({error})')
        commands.append(f'  checkFailure (← load folder "{label}") {limits} {prefix} (.group 1 ({error}))')
    schema, logical = expected["optional_v2_1111"]
    batches = IPC["batches_term"](schema, logical)
    for label in ("other_codec", "dictionary"):
        commands.append(f'  checkRows (← load folder "{label}") {batches}')

    driver = folder / "TwoListStructSnappy.lean"
    driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    ipc = {}
    for label, (schema, logical) in expected.items():
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            name = f"{label}_{selection}"
            output = ipc[name] = (folder / f"{name}.arrow").read_bytes()
            IPC["inspect_ipc"](output, projected, logical)
    for selection in ("field", "empty"):
        assert ipc[f"mixed_versions_and_codecs_{selection}"] == ipc[f"uncompressed_reference_{selection}"]
        assert ipc[f"v2_raw_bypass_{selection}"] == ipc[f"per_child_v2_{selection}"] == ipc[f"optional_v2_1111_{selection}"]
    print(f"Checked {len(positives)} sources, {counts['v1']} V1 and {counts['v2']} V2 frames, "
          f"{counts['v2_raw_words']} Snappy false-flag V2 suffixes with signed words, "
          f"{len(ipc)} strict IPC streams and {len(errors)} typed controls")
    pins = NATIVE["fingerprints"]
    return {key: pins(data) for key, data in {
        "genuine_parquet": originals, "authored_parquet": authored, "genuine_probes": probes, "lean_ipc": ipc,
    }.items()}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert BASE["producer"]() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {key: data for key, data in pins.items() if key != "producer"}


if __name__ == "__main__":
    main()
