# Checked Parquet BYTE_ARRAY dictionary fallback

`Silmaril.Formats.Parquet.ByteArrayFallback` reads one named optional
physical BYTE_ARRAY leaf of a flat Parquet snapshot. `openFile` reuses
the checked BYTE_ARRAY binding and file limits. `readGroup` uses the
selected leaf's original column ordinal at the requested footer group.
Payload validation covers that column. Present slots contain opaque bytes.

The profile is codec 0, V1 with flat RLE levels or V2 with flat levels.
An optional single leading dictionary page uses PLAIN tag 0. Data frames
use PLAIN tag 0 or RLE_DICTIONARY tag 8, selected from each original
typed header. Tag 8 requires the same chunk's leading dictionary. The
footer encoding list admits only 0, 3 and 8 and must advertise each
actual value tag. Tag 3 is a level encoding in this profile.
The reader rejects CRC-bearing pages, index pages,
nonleading dictionaries, legacy tag 2, and chunks without a data frame.

The reader checks chunk bounds, declared row counts and page and
dictionary limits before materializing the corresponding bodies. It
dispatches once per admitted frame. The first page failure after chunk
framing and count checks carries the original group, column, frame
ordinal, and header offset. A leading dictionary occupies frame ordinal
zero when present. A row group is returned only after all its selected
pages succeed.

`readGroup_wire` ties the original leaf, group, column and
`Page.readChunk` equation to the same immutable snapshot. The leading
dictionary's exact body yields the ordered PLAIN entries. For each
original data frame, the wire relation retains the exact body and
definition mask. The PLAIN branch consumes the exact value suffix and
the dictionary branch relates every ordered index to its original
entry. The resulting nullable slots are concatenated in frame order
and equal the footer group count.

## Fixtures

PyArrow 26.0.1 writes and independently reads two 384-row groups in
each clean file. Both groups select column 1 after an INT32 decoy.
Thrift 0.25.0 inspects the original frame boundaries and counts one
leading PLAIN dictionary, 17 tag-8 data frames and seven tag-0 data
frames in every selected chunk. The two dictionaries differ across
groups, and the rows include nulls and non-UTF-8 bytes.

The three V2 controls leave group 0 readable. In group 1, omitting the
dictionary from the declared span fails at frame 0, header 15111.
Changing a later PLAIN page tag to 3 fails at frame 19, header 16814.
Changing a final PLAIN length word fails at frame 24, header 22513.
PyArrow independently rejects each damaged group.

| File | SHA-256 |
| --- | --- |
| byte-array-fallback-v1.parquet | `7e2daecc0b67ed06ac25902eceaa777378413a0448d3d3872e2d42af52882b09` |
| byte-array-fallback-v2.parquet | `40d4e2f55d2b718bec8eeed69b4d58308ee4199f67e5be4983e9bfdfc339d7ee` |
| byte-array-fallback-v2-missing-dictionary.parquet | `5d73a8ac69fe8490b2e5276bcdceb201986abb8a3b6fa73479ac27140fed5feb` |
| byte-array-fallback-v2-bad-tag.parquet | `ad87729c086fc12f3fed424f6bd7c59b8874ab469ccfb6c8048224d2980faa08` |
| byte-array-fallback-v2-bad-length.parquet | `b70c6c3010fd442210464c9f60f86d1abef3be5f7805cec43179741a2637b8d6` |

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-byte-array-fallback/Oracle.py "$fixture_tmp"
diff -r data/parquet-byte-array-fallback "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-byte-array-fallback/Axioms.lean
```

## Selected whole-file events

`Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs` exposes
`openSource` and `readAll` for the same named optional leaf. `openSource`
uses the checked fallback open and its file byte and total row caps,
then supplies the common `Reader.Source` with the original footer
ordinals and the existing opaque BYTE_ARRAY row mapping. It can also
be consumed through `Reader.batchReader`.

The trace has one batch for each completely read group. An admitted
zero-row group contributes an empty batch in its original position.
The first failure keeps the preceding batches and carries the
original `ByteArrayFallback.Error` in `File.Error.readFailure`.
`File.readAll_order`, `File.readAll_success`, `File.readAll_first_error`
and `File.batch_slots` state these contracts.

The source tests reuse the five fallback fixtures for exact `[384, 384]`
batches and the original indexed errors after `[384]`. A total cap of
767 on the damaged 768-row files fails at open. The existing
[framed empty-middle fixture](parquet-int32-byte-array-file.md#producer-fixtures)
gives `[3, 0, 2]` at EOS and `[3, 0]` when the final group's binary
tag is changed to 3.

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.File.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-byte-array-fallback-file/Axioms.lean
```

## Opt-in parquet-java V1 fallback

`ByteArrayFallback.readLegacyGroup` uses the checked optional BYTE_ARRAY
binding and the existing bounded chunk walk for codec 0. It admits the
parquet-java V1 combination of a leading tag-2 dictionary and data tags
2 and 0. The dictionary body contains PLAIN length-prefixed entries.
Data pages use V1 definition tag 3 and repetition tag 4. The matched
flat leaf has maximum repetition level zero, so the existing scalar
adapter receives tag 3 for that absent repetition section.
`legacy_parameters_wire` relates this adapter parameter to the original
header and preserves the value tag, sizes and count. `readLegacyGroup_wire`
retains the original selected snapshot, ordered frames, chunk-local
dictionary lookups and PLAIN suffixes.

The producer is parquet-java 1.16.0, commit
`402c3810c372d29603e181771acebfecc71bef61`. The Thrift 0.25.0 oracle
sorts the footer encoding lists because parquet-java serializes them
in JVM-dependent order. All original page bytes and offsets are
preserved. The selected chunk's dictionary header is at byte 1900.
Its data section begins at 1937 and has ten tag-2 pages followed by
nine tag-0 pages. PyArrow 26.0.1 reads all 384 original slots and
rejects the damaged final PLAIN length. Lean reports the damage at
group 0, column 1, frame 19, header byte 10089.

| File | SHA-256 |
| --- | --- |
| parquet-java-v1-legacy-fallback.parquet | `63231c6286d24acc8ff3fcbf72b0641fb861dd7a78eec9908899cc9b14c07135` |
| parquet-java-v1-legacy-fallback-bad-length.parquet | `ba08f3886655f91c488e2b8e93b9bccca4ef87eb5ec4d1dbb0126cbd78dde9a1` |

Run from the repository root with JDK 21, Maven, PyArrow 26.0.1 and
Thrift 0.25.0.

```sh
fixture_tmp=$(mktemp -d)
mvn -B -q -f scripts/parquet-dictionary-chunk/pom.xml \
  org.apache.maven.plugins:maven-dependency-plugin:3.8.1:build-classpath \
  -Dmdep.outputFile="$fixture_tmp/classpath"
java -cp "$(cat "$fixture_tmp/classpath")" scripts/parquet-byte-array-legacy-fallback/WriteFallback.java "$fixture_tmp"
python3 scripts/parquet-byte-array-legacy-fallback/Oracle.py "$fixture_tmp"
for fixture in data/parquet-byte-array-legacy-fallback/*.parquet; do
  cmp "$fixture" "$fixture_tmp/$(basename "$fixture")"
done
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.LegacyTests
```

### Legacy whole-file events

`ByteArrayFallback.File.openLegacySource` and `readAllLegacy` select the
parquet-java V1 profile through the same checked source and file limits.
`readAllLegacy_success` preserves one batch per successfully decoded
footer group and its opaque slots. `readAllLegacy_first_error` preserves
the preceding complete batches and wraps the original indexed cause
in `File.Error.readFailure`. An admitted zero-row group emits its own
empty batch before the next footer group.

The Thrift 0.25.0 oracle copies the pinned parquet-java 1.16.0 chunk
bytes into groups 0 and 2 and supplies explicit zero-row PLAIN V1
frames for group 1. It relocates the chunk offsets and omits the
detached page indexes. The producer page headers and bodies in both
nonempty groups are byte-identical to the pinned source. PyArrow 26.0.1
independently checked the slots and group counts.

The clean fixture emits `[384, 0, 384]` and EOS. The damaged fixture
changes only the final PLAIN value length and emits `[384, 0]` before
the original error at group 2, column 1, frame 19, header byte 21009.
A total cap of 767 on that 768-row file fails at open.

| File | SHA-256 |
| --- | --- |
| legacy-v1-empty-middle.parquet | `67a4029e7ff4afcd9e3c88e1a335d22e4c52ef9d16ebd9e324b61e935d1e91a5` |
| legacy-v1-late-error.parquet | `58a6f17e3547e743c6dad6c66d4306a9f843875ecb438862bbd36e0c44036a77` |

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-byte-array-legacy-events/Oracle.py "$fixture_tmp"
diff -r data/parquet-byte-array-legacy-events "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.File.LegacyTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-byte-array-fallback-file/Axioms.lean
```

### Filter and project legacy events

`ByteArrayFallback.File.scan_readAllLegacy_order` composes the checked
legacy source with `Arrow.Events.EventStream.scan`. Each successfully
decoded group contributes a batch. The predicate sees the original row,
keeps only true results, and runs before the projection. This preserves
footer group positions even when a filter removes every row in a group
or the projection selects zero columns. The trace keeps its terminal cause.
`scan_readAllLegacy_first_error` states the exact filtered and projected
prefix for an original indexed group failure.

The scan regressions reuse both legacy event fixtures. Keeping all rows
with a zero-column projection produces counts `[384, 0, 384]` at EOS and
`[384, 0]` on the damaged file. Keeping values longer than eight bytes
produces `[118, 0, 118]` or `[118, 0]` with either the original field or
zero columns. An unknown predicate on every row gives `[0, 0]` before the
same original group 2, column 1, frame 19, header 21009 error.

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.File.ScanTests
```

## Opt-in Snappy fallback to native BinaryView

`ByteArrayFallback.Snappy.convert` selects one named flat optional
unannotated BYTE_ARRAY leaf from a checked Parquet snapshot. Parquet
BINARY uses the BYTE_ARRAY physical type with no logical or converted
annotation. The reader checks that fields 10 and 6 are both absent
from the original selected schema element. It returns the original
name and nullability in a native Arrow IPC V5 BinaryView field.
Dictionary entries and PLAIN slots stay opaque bytes throughout.

The selected codec-1 chunk requires a leading tag-0 dictionary, a
nonempty tag-8 data prefix, and a nonempty PLAIN suffix. The checked
phase walk rejects a return to tag 8. V1 checks the original CRC and
expands the whole stored body. V2 checks the CRC over the whole stored
body, retains the raw levels, and selects the index or value codec
from the original compression flag. Stored and expanded byte totals
include page headers and agree exactly with the selected footer chunk
under their respective limits.

The native readback law connects the original dictionary and PLAIN
bytes to the exact nullable slots of each group through EOS. The first
indexed source failure precedes IPC admission. Selection and annotation
checks apply to the one requested column.

PyArrow 26.0.1 produces genuine V1/V2 files with and without CRC.
Thrift 0.25.0 observes five tag-8 data pages then four PLAIN pages in
each of two 66-row groups. The V2 PLAIN suffix contains compressed
and raw pages. PyArrow independently compares every BinaryView slot
with its source read, including invalid UTF-8, NUL, null versus empty,
and 12-byte and longer values. Controls cover the source caps and
original late length, index, CRC and footer errors. The independently
assembled transition control swaps two intact frames with valid CRCs.
The annotation controls use one STRING file and a converted-only edit.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Snappy/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Snappy/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-snappy-fallback-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Checks
python3 scripts/parquet-snappy-fallback-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in Snappy dictionary-only BinaryView

`ByteArrayFallback.Snappy.Dictionary.convert` uses the same named flat
optional unannotated BYTE_ARRAY binding, checked byte extents and
native BinaryView writer. The selected codec-1 chunk must contain a
leading PLAIN dictionary (tag 0) and only RLE_DICTIONARY data pages
(tag 8). A PLAIN data page returns its original group, column, page
ordinal and header offset with an encoding refusal. The readback law
links the original annotation-free leaf, stored and expanded frame
extents, CRCs and ordered dictionary lookups to the exact nullable
bytes in each native batch through EOS.

PyArrow 26.0.1 produces genuine dictionary-only V1 and V2 files with
and without CRC. Thrift 0.25.0 checks the original footer and page
headers, exact dictionary octets, both V2 compression flags, raw V2
levels and original index streams. The native comparison covers
`[257, 129]` rows with NUL, empty and null slots, and non-text bytes.
Separate genuine V1 and V2 files both contain an all-dictionary first
group followed by a group with tag-8 pages and a PLAIN suffix. The
source returns the first PLAIN header as an indexed error before IPC
limits. Additional edits exercise a late out-of-range index and CRC
failure, and a producer STRING file exercises annotation refusal.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Snappy/Dictionary/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Snappy/Dictionary/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-snappy-dictionary-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Checks
python3 scripts/parquet-snappy-dictionary-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V1 dictionary-only BinaryView

`ByteArrayFallback.Gzip.Dictionary.convert` selects one named flat optional
BYTE_ARRAY leaf whose original logical and converted annotations are both
absent. The selected codec-2 chunk must start with a PLAIN dictionary
(tag 0). Data frames must record V1, RLE definition and repetition encodings,
and RLE_DICTIONARY (tag 8). A V2 frame or PLAIN fallback produces a typed
refusal at its original frame. Only the selected column's pages are decoded.

The reader checks each original stored body and its Parquet CRC when present.
Each dictionary and V1 data body must be exactly one GZIP member, including its
trailer, within the declared and capped byte extents and per-member call
budget. The expanded V1 body yields the original definition levels and
dictionary index stream. Native BinaryView emits the opaque slots in footer
group order through EOS, with distinct null and empty values. The first
indexed source failure precedes IPC admission.

PyArrow 26.0.1 produces two nine-row V1 groups with and without CRC. Thrift
0.25.0 reads one tag-0 dictionary and two tag-8 V1 pages per group. Python's
zlib checks exact single-member extents, and PyArrow independently compares
the native BinaryView IPC against the selected source rows, including bytes
that are invalid UTF-8. A genuine V2 file and a genuine later PLAIN fallback
exercise profile refusals. An assembled trailing-member edit preserves
framing by updating the original page and footer extents. A late stored-body
edit exercises CRC precedence, and a zero-call limit exercises the original
dictionary budget refusal. A producer STRING file exercises annotation refusal.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dictionary/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dictionary/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-dictionary-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Checks
python3 scripts/parquet-gzip-dictionary-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V1 dictionary-to-PLAIN BinaryView

`ByteArrayFallback.Gzip.Fallback.convert` uses the checked optional
unannotated BYTE_ARRAY binding and GZIP limits from the dictionary-only
profile. Each selected codec-2 chunk must have an original leading tag-0
dictionary, a nonempty V1 tag-8 data prefix, and a nonempty V1 tag-0 data
suffix. The reader preflights the original tag schedule before decoding
bodies. A return to tag 8 gives an indexed error at that header.

Each original frame consumes one complete GZIP member with the declared
expanded extent. The reader checks stored CRCs when present, stored and
expanded byte budgets, and the per-member call cap. The page witnesses
retain the original V1 levels and either the ordered dictionary lookups
or the exact PLAIN values. Native BinaryView preserves nullable opaque
bytes in footer group order through EOS. A source failure returns its
original indexed cause before IPC admission.

PyArrow 26.0.1 produces genuine fallback in two V1 groups of 64 and 72
rows, with and without CRC. Thrift 0.25.0 records five tag-8 pages in each
group, followed by three and four tag-0 pages respectively. Python zlib
checks exact member boundaries, and PyArrow compares the native IPC with
its own row-group readback, including invalid UTF-8, NUL, empty and null
values. Genuine V2 and dictionary-only inputs exercise profile refusals.
Assembled controls exercise a late CRC mismatch, a trailing GZIP member,
and reentry by swapping two intact CRC-valid frames.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Fallback/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Fallback/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-fallback-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Checks
python3 scripts/parquet-gzip-fallback-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V1 per-group BinaryView dispatch

`ByteArrayFallback.Gzip.Dispatch.convert` selects one flat optional
unannotated BYTE_ARRAY leaf. It frames each original codec-2 chunk once.
A recorded V1 PLAIN data header selects the strict fallback reader. All
other frame lists go to the strict dictionary-only reader. The choice
uses only original headers. The chosen reader checks its own admission,
receives the original frame list, and returns its result directly.

The agreement law compares the complete result, including every indexed
failure, with the corresponding strict entry point on the same snapshot.
The wire laws retain the original stored CRCs, the byte caps and
one-member GZIP extents, and the exact nullable slots in footer order.
Native BinaryView readback consumes EOS. The first source failure takes
precedence over IPC admission.

PyArrow 26.0.1 produces native mixed files with and without page CRC.
Thrift 0.25.0 observes dictionary-only, fallback, dictionary-only groups
of 40, 64 and 48 rows in the CRC file. The fallback group records five
tag-8 data pages and three tag-0 data pages. The no-CRC file has the first
two groups. Python zlib verifies the stored member extents. PyArrow
compares the actual Lean IPC with its own Parquet row-group readback,
including invalid UTF-8, NUL, null and empty values.

Assembled controls exercise a late dictionary-branch CRC failure, a
trailing member in a fallback page, reentry with intact CRC-valid frames,
and CRC failures in two groups to check first-error order.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dispatch/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dispatch/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-dispatch-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.Checks
python3 scripts/parquet-gzip-dispatch-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V2 dictionary-only BinaryView

`ByteArrayFallback.Gzip.Dictionary.V2.convert` selects one optional
unannotated BYTE_ARRAY leaf. Each selected codec-2 chunk admits a
leading PLAIN dictionary and RLE_DICTIONARY V2 data pages. The
dictionary consumes one complete GZIP member. The reader verifies CRC
over the original stored body, including the raw V2 definition prefix.
Flat repetition bytes must be zero and the definition extent must fit
both page sizes. The original `is_compressed` flag selects one complete
GZIP member or the exact raw bytes for the index suffix. The row mask,
index lookups, stored and expanded extents, and per-member limits are
checked against the original frames.

Native BinaryView preserves the selected nullable byte slots in footer
group order through EOS. The first indexed source error precedes IPC
admission. The V2 entry point returns typed refusals for V1 and PLAIN
data frames.

PyArrow 26.0.1 produces genuine dictionary-only V2 files with and
without page CRC. Thrift 0.25.0 observes flag sequences
`[true, true, false]`, `[true, false]`, and `[false]` for groups of
257, 129, and 128 rows, with an all-null final group. Independent
Thrift, RLE, and zlib checks recover raw levels and the exact dictionary
and index bytes. PyArrow compares the native IPC with the selected
source rows, including invalid UTF-8, NUL, null and empty values.

Assembled controls change a raw index, corrupt a raw definition prefix
under CRC, and append an empty member to a compressed V2 suffix.
The Lean oracle also checks a zero GZIP call cap on original raw and
compressed data pages. Genuine V1 and V2 fallback inputs exercise the
strict version and encoding gates.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dictionary/V2/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dictionary/V2/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-v2-dictionary-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2.Checks
python3 scripts/parquet-gzip-v2-dictionary-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V2 dictionary-to-PLAIN BinaryView

`ByteArrayFallback.Gzip.Fallback.V2.convert` selects one flat optional
unannotated BYTE_ARRAY leaf. Each selected codec-2 chunk begins with an
original PLAIN dictionary, then contains a nonempty prefix of tag-8 V2
data pages and a nonempty suffix of tag-0 V2 data pages. The reader checks
the original tag schedule before decoding any bodies. A return to tag 8
reports the original indexed header.

The original CRC covers the entire stored body for both encodings.
The raw definition section fits both declared sizes. The original
`is_compressed` flag selects either one complete GZIP member or the exact
raw suffix. The page laws connect those bytes to ordered dictionary
lookups or exact length-prefixed PLAIN values. Native BinaryView retains
opaque nullable bytes in footer group order through EOS. The first
indexed source error precedes IPC admission.

PyArrow 26.0.1 produces genuine fallback files with and without CRC.
Thrift 0.25.0 observes tags `[8, 8, 8, 0, 0]` and flags
`[true, false, false, true, false]` in both groups, with an all-null
dictionary-coded page. An independent RLE walk and Python zlib recover
the original levels and suffix bytes. PyArrow compares native Lean IPC
with its own selected Parquet rows, including invalid UTF-8, NUL, null
and empty values.

Assembled controls corrupt a raw definition prefix in each encoding
under CRC, alter a raw PLAIN length word, append an empty GZIP member to a
compressed PLAIN suffix, and move intact CRC-valid frames to create
dictionary reentry. The original compressed and raw PLAIN pages also
exercise the GZIP call cap. Genuine V1 fallback and the V2 dictionary-only
reader exercise the existing strict gates.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Fallback/V2/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Fallback/V2/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-v2-fallback-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Checks
python3 scripts/parquet-gzip-v2-fallback-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V2 per-group BinaryView dispatch

`ByteArrayFallback.Gzip.Dispatch.V2.convert` selects one flat optional
unannotated BYTE_ARRAY leaf. It frames each original codec-2 chunk once.
A recorded V2 PLAIN data header selects the strict V2 fallback callback.
All other frame lists go to the strict V2 dictionary callback. The chosen
callback validates its own profile and returns its complete result using
the original frame list.

The framed agreement law equates the complete result, including typed
errors, with the chosen strict reader on the same snapshot. Failures
before framing agree with both strict entry points. The group witnesses
retain original CRCs, raw levels, flag-selected suffix extents, and exact
nullable slots in footer order. Native BinaryView readback consumes EOS.
The first indexed source failure takes precedence over IPC admission.

PyArrow 26.0.1 produces genuine mixed files with and without page CRC.
Thrift 0.25.0 observes dictionary-only, fallback, and dictionary-only
groups of 40, 64, and 48 rows in the checksummed file. The fallback group
has five tag-8 pages with raw index suffixes followed by three tag-0
pages with GZIP suffixes. The no-CRC file has the first two groups.
Independent RLE and zlib checks verify the original raw levels and
suffix extents. PyArrow compares the native Lean IPC with its own
Parquet rows, including invalid UTF-8, NUL, null and empty values.

Assembled controls cover a late dictionary-branch CRC failure, a second
GZIP member in a compressed PLAIN suffix, dictionary reentry with intact
CRC-valid frames, and simultaneous CRC failures in different profiles.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dispatch/V2/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dispatch/V2/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-v2-dispatch-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.Checks
python3 scripts/parquet-gzip-v2-dispatch-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in GZIP V2 PLAIN-only BinaryView

`ByteArrayFallback.Gzip.Plain.V2.convert` selects one flat optional
unannotated BYTE_ARRAY leaf. Shared framing checks the original codec-2
chunk, footer offsets and row counts. The first framed data page must
start at the original data-page offset. A leading dictionary returns an
indexed refusal. Every admitted frame is PLAIN V2 and the footer
dictionary-page offset is absent.

The PLAIN callback checks the CRC of the original stored body, including
the raw definition levels. The original `is_compressed` flag selects one
complete GZIP member or the exact raw PLAIN suffix. The suffix and
definition witnesses recover the exact ordered nullable bytes under the
existing stored and expanded limits. Native BinaryView retains footer
group order through EOS. The first indexed source error precedes IPC
admission.

PyArrow 26.0.1 produces dictionary-free files with and without page CRC.
Thrift 0.25.0 sees groups of 65 and 33 rows, with flag sequences
`[true, true, false]` and `[true, false]`. Independent RLE and zlib checks
recover the original raw levels and exact PLAIN bytes. PyArrow compares
actual Lean IPC against its own selected source rows, including invalid
UTF-8, NUL, and empty and null values.

Assembled controls cover a raw-level CRC failure, a malformed raw PLAIN
length, and a second member after a compressed PLAIN suffix. Genuine
V1 and dictionary inputs exercise the strict gates, and the existing
two-way dispatcher continues to refuse the dictionary-free source.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Plain/V2/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Plain/V2/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-v2-plain-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Checks
python3 scripts/parquet-gzip-v2-plain-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in three-way GZIP V2 BinaryView dispatch

`ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.convert` selects one flat
optional unannotated BYTE_ARRAY leaf. The shared traversal frames each
original codec-2 chunk once. A leading dictionary selects the existing
dictionary-backed tag test. A V2 PLAIN header within that list selects
fallback, and the other dictionary-backed lists select dictionary-only.
Without a leading dictionary, the strict PLAIN-only callback decides
admission. The selected callback receives exactly the original frame
list, metadata and source bytes.

`readGroup_framed` connects the single framing result to the selected
callback. The agreement laws retain the exact strict result, including
failures before framing and the original indexed page cause after
framing. The group witnesses preserve CRCs, raw levels, flag-selected
suffixes and opaque nullable slots in footer order. Native BinaryView
readback consumes EOS. The first source failure precedes IPC admission.

PyArrow 26.0.1 produces three native inputs, one per strict profile.
The labeled mixed fixture copies their original row-group spans in
dictionary, PLAIN, fallback, dictionary order, with groups of 40, 65,
64 and 40 rows. Assembly relocates the Thrift footer offsets and
updates the group list, row count and producer label. The oracle compares every copied
column chunk against its native parent byte-for-byte. Thrift 0.25.0,
independent RLE and zlib check the schedules, flags, levels and CRCs.
PyArrow compares the actual Lean IPC with all native and assembled
selected rows.

Assembled controls exercise the original PLAIN and dictionary CRC
failures and a fallback reentry with intact CRC-valid frames. Two corrupt
groups check first-error order. A native PLAIN file exercises the
existing two-way entry point's strict refusal.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dispatch/V2/WithPlain/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Gzip/Dispatch/V2/WithPlain/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-gzip-v2-three-way-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.Checks
python3 scripts/parquet-gzip-v2-three-way-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in Zstandard V2 PLAIN-only BinaryView

`ByteArrayFallback.Zstd.Plain.V2.convert` selects one flat optional
unannotated BYTE_ARRAY leaf. The shared traversal checks the original
codec-6 chunk, offsets, aggregate extents, and row counts. A leading
dictionary returns its original indexed refusal. Every admitted data
frame is PLAIN V2 and the dictionary-page offset is absent.

The callback verifies the stored Parquet CRC before preparing values,
including the original raw definition-level prefix in that checksum.
The definition extent fits both declared sizes. The original
`is_compressed` flag selects either the exact literal suffix or one
complete frame in the existing checked, dictionary-free Zstandard
profile. Stored, expanded, window and command limits use the same
Zstandard preparation as the DATE reader. The PLAIN value witness
preserves exact opaque bytes and the original definition mask. The
first source failure precedes native IPC admission, and successful
footer-ordered BinaryView batches consume EOS.

PyArrow 26.0.1 produces genuine dictionary-free files with and without
page CRC. Thrift 0.25.0 observes flag sequences `[true, true, false]`
and `[true, false]` on 65 and 33 rows. Independent RLE, zlib and libzstd
1.5.7 check the raw levels, stored CRC, and exact frame boundary. PyArrow
compares Lean IPC with its own source rows, including non-UTF-8, NUL,
and empty and null values.

Labeled controls corrupt original raw levels, alter a literal PLAIN
length, append a second complete Zstandard frame, and mark an intact
literal suffix as compressed. A zero window budget admits the original
literal page and refuses the compressed page. Genuine V1 and dictionary
sources exercise the strict gates.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Zstd/Plain/V2/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Zstd/Plain/V2/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-zstd-v2-plain-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Checks
python3 scripts/parquet-zstd-v2-plain-binary-view-oracle/check.py "$(mktemp -d)"
```

### Opt-in Zstandard V2 dictionary-only BinaryView

`ByteArrayFallback.Zstd.Dictionary.V2.convert` selects one flat optional
unannotated BYTE_ARRAY leaf. Each codec-6 chunk has one leading PLAIN
dictionary and a nonempty sequence of tag-8 RLE_DICTIONARY Data Page V2
frames. The original chunk and frame extents, offsets, dictionary limits
and footer row counts are checked before IPC emission.

The dictionary uses one complete frame admitted by the bounded,
dictionary-free Zstandard decoder. The original stored CRC, when
present, covers the entire dictionary or data body and is checked
before expansion. Data definition levels remain raw. The original
`is_compressed` flag selects one complete checked Zstandard frame or the
literal width-prefixed Hybrid index stream. The decoder checks the exact
index count and extent, looks up each index in the original dictionary,
and reconstructs nullable slots in wire order. Successful conversion
writes those exact byte slots in footer-ordered BinaryView batches
through EOS. Indexed source failures precede IPC admission. V1 data and
PLAIN fallback return typed errors at their original frame coordinates.

PyArrow 26.0.1 produces dictionary-only V2 files with and without page
CRC and native examples of both data flags. Thrift 0.25.0, independent
Hybrid and CRC checks, and libzstd 1.5.7 verify the original dictionary,
index, level and stored-frame extents. PyArrow compares the resulting Lean
IPC with the input Parquet groups, including unused entries, all-null
data, present empty values, NUL and non-UTF-8 bytes. Native V1 and
dictionary-to-PLAIN inputs test strict refusal. Labeled mutations test a
bad dictionary CRC, a bad raw-level CRC, an out-of-range literal index
and a second complete Zstandard frame appended to a compressed suffix.

[Definitions](../../Silmaril/Formats/Parquet/ByteArrayFallback/Zstd/Dictionary/V2/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/ByteArrayFallback/Zstd/Dictionary/V2/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-zstd-v2-dictionary-binary-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Checks
python3 scripts/parquet-zstd-v2-dictionary-binary-view-oracle/check.py "$(mktemp -d)"
```
