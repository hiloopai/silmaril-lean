# Parquet STRING to native Arrow Utf8View

`Parquet.Plain.ByteArray.Utf8.convert` exports one named, flat,
required or optional BYTE_ARRAY leaf as an Arrow IPC V5 Utf8View
field. The checked PLAIN file reader supplies the original selected
groups under the usual file, row, and page caps. The physical profile
admits codec 0 and PLAIN Data Page V1 with the existing RLE level
contract or Data Page V2. The physical page checks reject CRC-bearing pages.

The annotation comes from the serialized leaf at the physical
binding's original column ordinal. The reader accepts three annotation forms.

- LogicalType field 10 with exactly STRING member 1 and an empty
  marker payload.
- ConvertedType field 6 with the UTF8 code 0, in the absence of
  LogicalType.
- Both of those forms together.

Both present fields must agree. A different or malformed modern
marker, a nonzero converted code, and a missing annotation each
produce a typed refusal. The source validity check runs before IPC
admission. After a complete physical group read, every present slot
is decoded with strict `String.fromUTF8?`. An invalid slot reports its
zero-based group and logical row position. Physical failures retain
their original indexed error. The opaque BYTE_ARRAY exporter exposes the same bytes as BinaryView.

`openFile_wire` ties the raw annotation and physical reader to the
same checked footer leaf. `readGroup_wire` retains the original
framed PLAIN group and proves that encoding the resulting nullable
strings recovers the original slot bytes. `convert_readback` ties
the native descriptor and all string batches through exact EOS to the
checked group list. `convert_first_error` preserves the first failed
group cause before IPC emission.

The oracle uses PyArrow 26.0.1 and Thrift 0.25.0. It independently
reads nullable and required STRING values from V1 and V2 producer
files, including distinct composed and decomposed spellings, nulls,
empty strings, multibyte values, and embedded NUL. The V2 empty group
gets an explicit zero-slot page per chunk via a Thrift edit, preserving
the original nonempty producer pages and `[5, 0, 4]` batch counts.
The late text edit changes a payload octet without changing the
lengths and fails at group 2, slot 1. A separate PLAIN length edit
fails at group 2, column 1, page 0, header offset 142. Footer edits
exercise modern-only, converted-only, missing, inconsistent, and
malformed annotations.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Checks \
  +Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Checks
python3 scripts/parquet-utf8-view-oracle/check.py "$(mktemp -d)"
```

## Opt-in Snappy PLAIN STRING

`Parquet.Plain.ByteArray.Utf8.Snappy.convert` uses the same checked
STRING annotation and strict UTF-8 decoder for a selected flat required
or optional BYTE_ARRAY leaf. This profile requires codec 1 and exact
PLAIN tag 0. V1 expands the whole page body with Snappy and reads RLE
levels. V2 checks the level lengths against both declared page sizes,
then reads the raw levels and decodes only the value suffix. The resolved
original V2 compression flag selects Snappy or a raw suffix. A present
CRC is verified over the complete stored body before decoding. Dictionary
pages and dictionary value encodings are outside this profile.

`readGroup_wire` joins the original frame list and stored payload spans
to the CRC decision, size caps, scalar preparation and exact nullable
UTF-8 octets. `convert_readback` preserves one native Utf8View batch per
footer group through EOS. The first failed group returns the original
indexed cause before IPC limits are applied. Invalid UTF-8 includes the
original group, column, page and header offset plus a zero-based logical
slot within that page.

PyArrow 26.0.1 produces V1 and V2 files both with and without CRC. Thrift
0.25.0 checks the selected leaf, page headers, CRCs, and exact payload
extents. V2 files contain both compressed and raw value suffixes. PyArrow
independently compares the decoded Parquet slots and Lean IPC batches
`[8, 1, 5]`, including null and empty strings, composed and decomposed
text, multibyte text and NUL. Controls exercise the later expansion cap,
CRC mismatch and invalid UTF-8 with exact page coordinates, along with
codec and dictionary admission.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Snappy/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Snappy/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-snappy-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.Checks
python3 scripts/parquet-snappy-utf8-view-oracle/check.py "$(mktemp -d)"
```

## Opt-in uncompressed dictionary STRING

`Parquet.Plain.ByteArray.Utf8.Dictionary.convert` binds one named flat
optional BYTE_ARRAY leaf with the same checked STRING/UTF8 annotation.
It reads codec 0, one leading PLAIN dictionary (tag 0) per selected
chunk, and only RLE_DICTIONARY data pages (tag 8). V1 uses RLE levels.
V2 uses the original raw level and index windows. Required leaves,
CRC, compression, legacy tag 2 and PLAIN fallback are outside this
profile. Admission and decoding apply to the selected column.

After the exact bounded PLAIN dictionary decode, the reader validates
each entry as strict UTF-8 in dictionary order before reading any of
its indices. Every dictionary entry is a value of the annotated STRING
leaf, so malformed unused entries fail the same check as referenced
entries. This gives a complete typed dictionary for the original chunk
and makes text validation independent of which rows use it. Invalid
text reports dictionary page 0, its original header offset and the
zero-based entry ordinal. Index failures carry the original data page
ordinal including the leading dictionary, and the original header offset.

`readGroup_wire` ties the bound snapshot and selected chunk to the
original frame order. Each dictionary entry encodes to its original
bytes, every data page retains its exact definition mask and consumed
index stream, and the indexed lookups recover the ordered nullable
UTF-8 octets. `convert_readback` preserves one native Utf8View batch
per group through EOS. Source failures precede IPC writer limits.

PyArrow 26.0.1 produces V1 and V2 files with two nine-row groups and
different dictionary orders. Thrift 0.25.0 checks exact tag-0 entries,
tag-8 indices, and nullable slot order. The IPC comparison covers
non-ASCII text, distinct composed and decomposed spellings, repeated
values, nulls and empty strings. Three edits in the second group
exercise invalid used entry 0, invalid unused entry 4, and out-of-range
index 7 on data page 2. The unused-entry edit leaves PyArrow's decoded
rows and the opaque reader's selected bytes identical to the clean file.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Dictionary/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Dictionary/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-dictionary-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Checks
python3 scripts/parquet-dictionary-utf8-view-oracle/check.py "$(mktemp -d)"
```

## Opt-in uncompressed dictionary-to-PLAIN STRING

`Parquet.Plain.ByteArray.Utf8.Fallback.convert` selects one named flat
optional BYTE_ARRAY leaf with the checked STRING/UTF8 annotation. Its
codec-0 V1/V2 chunks require one leading PLAIN dictionary (tag 0), a
nonempty prefix of RLE_DICTIONARY data pages (tag 8), and a nonempty
suffix of PLAIN data pages (tag 0). It checks the original header
sequence before decoding bodies. A return to tag 8 reports that page's
original ordinal and header offset. A missing phase is an encoding
refusal at the selected column. CRC, compressed chunks and legacy
dictionary tags are outside this profile.

The reader uses the shared checked traversal, validates every dictionary
entry with the strict STRING dictionary reader, then decodes data from
the original frame and tag. Each present PLAIN slot is checked as strict
UTF-8 and errors name its zero-based logical slot, including any preceding
nulls. `readGroup_wire` ties both nonempty phases to the original selected
chunk, dictionary, definition masks, and nullable octets. `convert_readback`
retains the ordered batches through native IPC EOS. The complete source
must succeed before the writer applies IPC limits.

PyArrow 26.0.1 produces both positive files directly. Thrift 0.25.0
observes five tag-8 pages followed by three PLAIN pages in each of two
64-row groups for both V1 and V2. PyArrow compares the original file with
the Lean-emitted Utf8View IPC, including nulls, empty values, repeated text
and distinct composed and decomposed spellings. The V2 negative controls
edit the second group. One changes the sole reference to entry 4 and then
corrupts that now-unused entry. One corrupts PLAIN logical slot 4 after a
null without changing its length. The transition control swaps two complete
producer frames and independently checks both intact bodies in their new
order. Separate PLAIN-only and dictionary-only files exercise missing phases.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Fallback/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Fallback/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-fallback-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Checks
python3 scripts/parquet-fallback-utf8-view-oracle/check.py "$(mktemp -d)"
```

## Opt-in Snappy dictionary STRING

`Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.convert` selects one
named flat optional STRING/UTF8 BYTE_ARRAY leaf. Its codec-1 chunks
require one leading PLAIN dictionary (tag 0) and only RLE_DICTIONARY
data pages (tag 8). V1 expands the complete body and reads RLE levels.
V2 retains the original raw definition levels and lets the original
compression flag select Snappy or raw decoding of the index suffix.
The profile verifies any CRC over the entire stored body before expansion,
including the raw levels in V2. PLAIN fallback and legacy dictionary
tags are separate profiles.

The selected chunk uses separate stored and expanded caps. The stored
extent is the sum of original header and stored body lengths. The
expanded extent sums those same headers and declared expanded bodies,
checks the expanded cap before decoding, and requires the exact footer
size. The dictionary also has entry-count, stored-byte, expanded-byte
and individual value limits. The read validates every dictionary entry
as strict UTF-8, including unused entries.

`readGroup_wire` retains the original chunk and exact byte totals, a
CRC-checked dictionary that round-trips all entries, and original data
frames with exact level masks and index streams. `convert_readback`
preserves the original nullable octets and group boundaries through
native IPC EOS. The first source failure preserves the original indexed
cause before writer limits are applied.

PyArrow 26.0.1 produces genuine V1 and V2 Snappy dictionary files with
and without CRC, and both V2 compression flags occur. Thrift 0.25.0
checks the stored and expanded chunk totals, CRCs, and original page
headers. Independent decoding compares all `[257, 129]` nullable slots
with Lean's native Utf8View batches, including distinct composed and
decomposed strings and empty values. The edits exercise invalid unused
UTF-8, out-of-range indices, the original dictionary and data CRC
errors, and a false expanded footer size. Separate controls check both
page and chunk caps before IPC admission.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Dictionary/Snappy/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Dictionary/Snappy/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-snappy-dictionary-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Checks
python3 scripts/parquet-snappy-dictionary-utf8-view-oracle/check.py "$(mktemp -d)"
```

## Opt-in Snappy dictionary-to-PLAIN STRING

`Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.convert` selects one flat
optional STRING/UTF8 BYTE_ARRAY leaf. It requires codec 1, a leading
PLAIN dictionary, a nonempty tag-8 data prefix and a nonempty tag-0
suffix. The same one-way phase check as the uncompressed profile
runs on original headers before body decoding, with an indexed error
for a return to tag 8. Stored and expanded chunk totals include the
original header bytes and must match the footer under separate caps.

The reader checks every dictionary entry as strict UTF-8 and keeps
all dictionary and data bodies attached to their original CRC and
byte limits. V1 expands the complete body and reads RLE levels.
V2 retains the raw definition levels and uses the original flag for
the index or value suffix. It verifies any CRC over the entire stored
body before decoding and validates each present PLAIN value as strict
UTF-8. PLAIN text failures use the original page-relative logical
slot, including any preceding nulls.

The wire laws tie both data phases to the original selected chunk and
preserve the exact nullable UTF-8 octets and group boundaries through
native IPC EOS. The first indexed source error takes precedence over
IPC admission.

PyArrow 26.0.1 produces V1 and V2 files with and without CRC. Thrift
0.25.0 observes five dictionary pages then four PLAIN pages in each
of two 66-row groups. The V2 PLAIN suffix includes three compressed
pages and one raw page. PyArrow compares the original Parquet values
with each Lean IPC batch. The edited V2 controls cover a late invalid
PLAIN value at logical slot 1 after a null, the same edit under CRC,
a bad expanded footer total, and the late PLAIN expansion cap. Two
independently assembled controls redirect the sole index away from
an invalid dictionary entry and swap two intact frames to return to
tag 8 with both CRCs still valid. Separate producer files cover either
missing phase.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Fallback/Snappy/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Fallback/Snappy/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-snappy-fallback-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Checks
python3 scripts/parquet-snappy-fallback-utf8-view-oracle/check.py "$(mktemp -d)"
```

## Native Utf8View to Parquet STRING

`Parquet.Plain.ByteArray.Utf8.FromIpc.convert` reads one explicitly
declared Utf8View field through exact Arrow IPC EOS. The writer uses
the field's original name and nullability and emits one uncompressed
PLAIN V1 BYTE_ARRAY page per batch. The footer writes both the empty
modern STRING marker and converted UTF8 code 0.

The output uses the strings' existing UTF-8 octets. Null and empty
strings have distinct slots. Every explicit batch has a row group,
including a zero-row batch with a real page header. A schema-only
stream writes the declared STRING leaf with zero groups. File, group,
row, chunk, page, value and footer budgets govern writing. The writer
measures page spans and budgets the footer before materializing page
bodies. It returns a file only after the checked STRING reader
recovers the original annotation and all batches.

`convert_readback` links the complete native source, including its
original schema and record windows through EOS, to the checked
Parquet file. `SinkWire` records one group per source batch and the
exact original nullable UTF-8 octets in its framed PLAIN chunk.
`convert_source_error` preserves the original native IPC failure.

Pinned PyArrow 26.0.1 produces the input streams and reads the output
Parquet with the original text and batch boundaries. Thrift 0.25.0
checks the leaf markers, every original chunk offset, and the complete
PLAIN page bodies with exact UTF-8 lengths and definition levels.
The optional and required cases have group counts `[5, 0, 4]` and
`[2, 0, 2]`. The comparison covers composed and decomposed spellings,
multibyte text, embedded NUL, and the distinction between null and
an empty string. Separate controls exercise source truncation,
invalid UTF-8 in the last source batch, explicitly binary input,
and writer budgets.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/FromIpc/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/FromIpc/Thms.lean) ·
[Fixture hashes](../../scripts/utf8-view-to-parquet-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Checks
python3 scripts/utf8-view-to-parquet-oracle/check.py "$(mktemp -d)"
```
