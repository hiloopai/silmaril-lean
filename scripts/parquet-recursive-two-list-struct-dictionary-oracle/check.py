"""Check original signed TwoListStruct dictionary frames, indices and slots."""

from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-snappy-oracle/check.py"))
DICTIONARY = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-dictionary-oracle/check.py"))
BASE, NATIVE, IPC, THRIFT, LEAN = (SNAPPY[key] for key in ("BASE", "NATIVE", "IPC", "THRIFT", "LEAN"))
encode, header_body, raw_chunks, repack = (SNAPPY[key] for key in ("encode", "header_body", "raw_chunks", "repack"))
authored_page, suffix_start = DICTIONARY["authored_page"], DICTIONARY["suffix_start"]
ALL = (True,) * 4
LATE = (1, 1)


LEAN = LEAN.rsplit("set_option maxHeartbeats", 1)[0] + """
private def checkDictionary (file : Bytes) (group : Nat) (side : Side) (frame : Page.Frame)
    (entries : List RecursiveSchema.Chunk.Word) (indices : List (Nat × List Nat)) : IO Unit := do
  let source ← take (openFile {} file)
  let bound ← take (Reader.bindGroup source.snapshot group)
  let column ← take (Reader.bindColumn source.schema bound side)
  let observed ← take (Reader.readColumn {} column)
  let some table := observed.dictionary | throw (IO.userError "missing checked dictionary")
  unless table.frame = frame && table.codec = .uncompressed && table.entries.toList = entries &&
      column.span.start = frame.header.start &&
      column.column.metadata.dictionaryPageOffset = some (Int.ofNat frame.header.start) &&
      column.column.metadata.dataPageOffset = Int.ofNat frame.payload.stop &&
      observed.pages.head?.map (·.frame.header.start) = some frame.payload.stop do
    throw (IO.userError "original dictionary frame, entries or anchors differ")
  for (ordinal, expected) in indices do
    let some page := observed.pages[ordinal]? | throw (IO.userError "missing original data page")
    let suffix := bytesAt file page.decoded.sections.values
    let physicalWords := page.decoded.atoms.filterMap (·.word)
    let actual ← take (DictionaryIndex.readIndices ({} : Reader.Limits).indices physicalWords.length suffix)
    let selected ← take (DictionaryIndex.select table.entries actual)
    unless actual = expected && selected = physicalWords do
      throw (IO.userError "checked local indices or exact signed words differ")
"""


def native(flags, optional, version, **options):
    return SNAPPY["native"](flags, optional, version, **(dict(compression="NONE", use_dictionary=True) | options))


def frames(wire, key):
    return SNAPPY["frames_in"](wire, *key)


def encoding(header):
    if header[1][1] == 0:
        return header[5][1][2][1]
    assert header[1][1] == 3
    return header[8][1][4][1]


def fixtures():
    genuine, authored, positives, refusals = {}, {}, {}, []

    def keep(label, case):
        genuine[label] = positives[label] = case

    path = ".".join(NATIVE["PATH"])
    for version in (1, 2):
        keep(f"optional_v{version}", native(ALL, True, version))
        keep(f"required_v{version}", native((False, False, False, True), False, version, reverse=True,
                                           write_page_checksum=False))
        keep(f"fallback_v{version}", native(ALL, True, version, dictionary_pagesize_limit=16, data_page_size=16))
        child = "lo" if version == 1 else "hi"
        keep(f"one_child_v{version}", native(ALL, True, version, use_dictionary=[f"{path}.{child}"]))
        expected_col = version - 1
        assert [key for key, meta, _, _ in NATIVE["V2"]["columns"](genuine[f"one_child_v{version}"][2])
                if 11 in meta] == [(group, expected_col) for group in (0, 1)]

        schema = genuine[f"optional_v{version}"][0]
        zero = [[None, [], [None, [], [None, {"lo": None, "hi": None}]]]]
        wire = NATIVE["write"](schema, zero, data_page_version=f"{version}.0", use_dictionary=True,
                               max_rows_per_page=1, write_batch_size=1)
        keep(f"zero_values_v{version}", (schema, zero, wire))

    keep("snappy_plain_sibling", native(ALL, True, 2, use_dictionary=[f"{path}.lo"],
                                       compression={f"{path}.lo": "NONE", f"{path}.hi": "SNAPPY"}))
    assert [SNAPPY["column_codec"](genuine["snappy_plain_sibling"][2], (0, side)) for side in (0, 1)] == [0, 1]

    schema, groups, wire = genuine["optional_v1"]
    chunks = raw_chunks(wire)
    newer = raw_chunks(genuine["optional_v2"][2])
    trace = NATIVE["trace"]
    widths = NATIVE["WIDTHS"]
    pieces = {}
    tables = {}
    for side, width in enumerate(widths):
        key = 1, side
        original = chunks[key]
        words = header_body(original[0])[1]
        tables[side] = table = [word for word, in struct.iter_unpack("<i" if width == 32 else "<q", words)]
        first, middle, last = [trace([row], ALL, side, optional_element=True) for row in groups[1]]
        if side == 0:
            rep2 = next(i for i, atom in enumerate(first) if atom[0] == 2)
            rep1 = next(i for i, atom in enumerate(first) if atom[0] == 1)
            pieces[side] = [(first[:rep2], 1, 8), (first[rep2:rep1], 1, 0), (first[rep1:], 1, 8),
                            (middle, 2, 8), (last, 1, 0)]
        else:
            cut = next(i for i, atom in enumerate(first) if i >= 4 and atom[0] == 2)
            pieces[side] = [(first[:cut], 1, 8), (first[cut:], 1, 8), (middle, 2, 8), (last, 2, 8)]
        pages = []
        for slots, version, tag in pieces[side]:
            template = original[1] if version == 1 else newer[key][1]
            pages.append(authored_page(template, slots, table, encoding=tag, page_version=version, width=width))
        chunks[key] = [original[0], *pages]

    mixed = authored["mixed_versions_fallback"] = repack(wire, chunks)
    positives["mixed_versions_fallback"] = schema, groups, mixed

    def patch(label, ordinal, frame):
        edited = chunks | {LATE: [*chunks[LATE][:ordinal], frame, *chunks[LATE][ordinal + 1:]]}
        authored[label] = repack(mixed, edited)

    def refuse_page(label, ordinal, cause):
        refused = frames(authored[label], LATE)[ordinal][0]
        refusals.append((label, ordinal, refused, cause))

    for ordinal, version in ((2, 1), (4, 2)):
        header, body = header_body(chunks[LATE][ordinal])
        split = suffix_start(header, body)
        suffix = body[split:]
        assert len(suffix) >= 3 and suffix[0] == 8 and encoding(header) == 8
        out_of_bounds = len(tables[1])
        for reason, bad, cause in (
            ("out_of_bounds", suffix[:2] + bytes([out_of_bounds]) + suffix[3:], f".outOfBounds {out_of_bounds}"),
            ("trailing", suffix + b"\x02\0", ".hybrid .trailingBytes"),
        ):
            label = f"late_{reason}_v{version}"
            payload = body[:split] + bad
            patch(label, ordinal, encode(deepcopy(header), payload, len(payload)))
            refuse_page(label, ordinal, f".dictionaryIndices ({cause})")

    header, body = header_body(chunks[LATE][0])
    bad = bytes([body[0] ^ 1]) + body[1:]
    patch("late_dictionary_crc", 0, encode(header, bad, len(bad), crc=False))
    crc = header[4][1] & 0xffffffff
    dictionary_crc = f".checksum (.mismatch {crc} {zlib.crc32(bad)})"

    footer = NATIVE["metadata"](mixed)
    column = THRIFT["column_metadata"](footer, *LATE)
    original_offset = column[9][1]
    column[9] = TType.I64, original_offset + 1
    authored["late_data_anchor"] = NATIVE["TWO"]["SCHEMA"]["pack"](mixed, footer)

    last, version, tag = pieces[1][-1]
    shared = NATIVE["steps"](ALL)[2] + 1
    at = next(i for i, atom in enumerate(last) if atom[1:] == (shared, None))
    changed = last.copy()
    changed[at] = last[at][0], shared - 1, None
    patch("late_topology", 4, authored_page(chunks[LATE][4], changed, tables[1], encoding=tag,
                                            page_version=version, width=64))
    slot = sum(len(rows) for rows, _, _ in pieces[1][:-1]) + at
    point = NATIVE["point"]
    topology = (f".topology (.conflict {slot} {point(authored['late_topology'], 1, 0, slot)} "
                f"{point(authored['late_topology'], 1, 1, slot)} ({last[at][0]}, {shared}) ({last[at][0]}, {shared - 1}))")

    compressed = native(ALL, True, 2, compression="SNAPPY")[2]
    footer = NATIVE["metadata"](mixed)
    dest = THRIFT["column_metadata"](footer, *LATE)
    dest.clear()
    dest.update(THRIFT["column_metadata"](NATIVE["metadata"](compressed), *LATE))
    authored["late_compressed_dictionary"] = repack(mixed, chunks | {LATE: raw_chunks(compressed)[LATE]}, footer)

    addr = NATIVE["address"](*LATE)
    dictionary_at = frames(authored["late_dictionary_crc"], LATE)[0][0]
    chunk_errors = {
        "late_dictionary_crc": f".chunk (.dictionary {addr} 0 {dictionary_at} ({dictionary_crc}))",
        "late_data_anchor": (f".chunk (.dictionary {addr} 1 {original_offset} "
                             f"(.dataOffset {original_offset + 1} {original_offset}))"),
        "late_topology": topology,
        "late_compressed_dictionary": f".binding (.column {addr} (.encodings {SNAPPY['lst'](map(str, THRIFT['list_field'](dest, 2)))}))",
    }
    return genuine, authored, positives, compressed, refusals, chunk_errors


def table_term(dictionary):
    at, header, body_at, body, entries = dictionary
    info = header[7][1]
    sort = info.get(3)
    sorted_term = "none" if sort is None else f"some {str(sort[1]).lower()}"
    crc = "none" if 4 not in header else f"some {header[4][1] & 0xffffffff}"
    size = len(body)
    return (f"⟨⟨{size}, {size}, {crc}, .dictionary ⟨{len(entries)}, 0, {sorted_term}⟩⟩, "
            f"⟨{at}, {body_at}⟩, ⟨{body_at}, {body_at + size}⟩⟩")


def dictionary_commands(label, schema, wire, columns, dictionaries, counts):
    commands = []
    widths = [field.type.bit_width for field in schema.field(0).type.value_type.value_type]
    decode = NATIVE["V2"]["HYBRID"]
    for key, table in dictionaries.items():
        group, side = key
        width = widths[side]
        assert SNAPPY["column_codec"](wire, key) == 0
        counts["dictionaries"] += 1
        if not table[-1]:
            counts["empty_dictionaries"] += 1
        indices = []
        pages = columns[key][1]
        data_frames = frames(wire, key)[1:]
        for ordinal, (page, (_, header, _, _)) in enumerate(zip(pages, data_frames, strict=True)):
            if encoding(header) == 8:
                values = sum(atom[2] is not None for atom in page[-1])
                lo, hi = page[4][-2:]
                suffix = wire[lo:hi]
                found = decode(suffix[1:], suffix[0], values)
                indices.append(f"({ordinal}, {SNAPPY['lst'](map(str, found))})")
                if not found:
                    counts["zero_value_pages"] += 1
            else:
                counts["fallback"] += 1
        tag = ".left" if side == 0 else ".right"
        words = SNAPPY["lst"](f".int{width} ({word})" for word in table[-1])
        commands.append(f'  checkDictionary (← load folder "{label}") {group} {tag} {table_term(table)} '
                        f'{words} {SNAPPY["lst"](indices)}')
    return commands


def verify(folder):
    genuine, authored, positives, compressed, refusals, chunk_errors = fixtures()
    originals = {label: case[2] for label, case in genuine.items()}
    files = originals | authored | {"compressed_origin": compressed}
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code, entry, observations, counts = [LEAN], [], {}, Counter()
    for label, (schema, groups, wire) in positives.items():
        tables = {}
        commands, logical, columns, frame_counts = SNAPPY["source_commands"](
            label, schema, groups, wire, SNAPPY["decode_snappy"], checksums=not label.startswith("required_"),
            dictionaries=tables)
        observations[label] = schema, logical, columns
        counts.update(frame_counts)
        local = Counter()
        dictionary_checks = dictionary_commands(label, schema, wire, columns, tables, local)
        if label.startswith("fallback_"):
            assert local["fallback"] > 0
        if label.startswith("zero_values_"):
            assert local["empty_dictionaries"] == 2 and local["zero_value_pages"] > 0
        if label == "mixed_versions_fallback":
            lhs = columns[1, 0][1]
            assert [page[-1][0][0] for page in lhs[:3]] == [0, 2, 1]
            assert local["fallback"] > 0
        counts.update(local)
        code.extend([f"set_option maxHeartbeats 2000000 in\nprivate def verify_{label} (folder : System.FilePath) : IO Unit := do",
                     *commands, *dictionary_checks])
        entry.append(f"  verify_{label} folder")

    schema, logical, columns = observations["mixed_versions_fallback"]
    prefix = IPC["batches_term"](schema, logical[:1])
    addr = NATIVE["address"](*LATE)
    code.append("private def controls (folder : System.FilePath) : IO Unit := do")
    for label, ordinal, byte, cause in refusals:
        cursor = SNAPPY["triple"](columns[LATE][1][ordinal - 1][-3])
        chunk_errors[label] = f".chunk (.page {addr} {ordinal} {byte} {cursor} ({cause}))"
    for label, cause in chunk_errors.items():
        code.append(f'  groupRefusal (← load folder "{label}") 1 {{}} ({cause})')
        code.append(f'  checkFailure (← load folder "{label}") {{}} {prefix} (.group 1 ({cause}))')
    code.extend(['public def main (args : List String) : IO Unit := do',
                 '  let [folder] := args | throw (IO.userError "expected fixture directory")',
                 *entry, "  controls folder"])
    NATIVE["V2"]["run_lean"](folder, "TwoListStructDictionary.lean", code)

    ipc = {}
    for label, (schema, logical, _) in observations.items():
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            name = f"{label}_{selection}"
            output = ipc[name] = (folder / f"{name}.arrow").read_bytes()
            IPC["inspect_ipc"](output, projected, logical)
    for selection in ("field", "empty"):
        expected = ipc[f"optional_v1_{selection}"]
        for label in ("optional_v2", "mixed_versions_fallback", "one_child_v1", "one_child_v2", "snappy_plain_sibling"):
            assert ipc[f"{label}_{selection}"] == expected
    print(f"Checked {len(positives)} carriers, {counts['dictionaries']} original dictionaries "
          f"({counts['empty_dictionaries']} empty), {counts['v1']} V1 and {counts['v2']} V2 frames, "
          f"{counts['fallback']} PLAIN fallback frames, {counts['zero_value_pages']} zero-value index sections, "
          f"{len(ipc)} exact IPC streams and {len(chunk_errors)} typed controls")
    pins = NATIVE["fingerprints"]
    return {"genuine_parquet": pins(originals | {"compressed_origin": compressed}),
            "authored_parquet": pins(authored), "lean_ipc": pins(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert BASE["producer"]() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {key: data for key, data in pins.items() if key != "producer"}


if __name__ == "__main__":
    main()
