# Checked native Parquet writer for nullable INT32 LIST

`Parquet.ListFile.Writer.emit` writes one optional LIST column
with an optional signed INT32 element. It preserves the supplied
outer name and requires the supplied child name to be `element`,
as required by the admitted canonical reader. The three-level
schema writes the modern LIST annotation and its matching converted
code. Each requested group has one complete uncompressed, CRC-free
PLAIN Data Page V1. The column path is the original outer name,
`list`, and `element`. No list continues across pages in this
writer profile.
[Pinned LIST layout](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#lists) · [Pinned Thrift and V1 header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L697-L723)

The writer projects the existing `ListPage.rowEvents` wire
classification to two singleton-run Hybrid streams and an exact
PLAIN suffix. A null list and an empty list contribute definition
levels 0 and 1, respectively, with repetition zero. A null child
contributes definition level 2. A present signed child contributes
definition level 3 and one PLAIN word in original order. Repetition
one follows the first element of an already opened list. The
per-page V1 length words delimit the repetition and definition
streams. This singleton-run encoding emits no padded logical
slots.
[Pinned Hybrid wire](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#run-length-encoding--bit-packing-hybrid-rle--3) · [LIST page decoder](parquet-list-v1.md)

The writer measures slots, values and page sizes before allocating
the body buffers. It checks signed V1 counts and body extents,
per-page and aggregate caps, and the complete file and footer budgets.
It reuses the existing V1 header, signed PLAIN encoder, Hybrid run
wire model and bounded Compact serialization primitives. Each
chunk's advertised value count is its number of level slots. Row
counts are kept separately. The returned file checks original
absolute chunk and frame positions, matching body slices, ordered
contiguous data extents, and the exact footer and trailer.

A zero-length group list produces a schema-only file. An explicit
empty group emits an actual zero-slot page with two zero length
words, producing one empty readback group. The writer never represents
that group with a zero-byte chunk. The canonical multi-frame LIST
reader checks the completed file and must recover the exact input
names and ordered groups before emission succeeds.
[Existing LIST file reader](parquet-list-continuation.md)

`PageEncoding.body_wire` gives a direct wire witness for the original
ordered LIST slots, including both Hybrid streams and the signed PLAIN
suffix. `checkInput_exact`, `PageEncoding.measure_fits`, `emit_exact`
and `emitted_frame` cover resource guards, exact page and file layout,
and complete checked boundaries. `emit_readback` gives same-file
footer and per-group witnesses from the native reader and preserves
the difference between a schema-only file and an actual empty group.
[Public API and theorems](../../Silmaril/Formats/Parquet/ListFile/Writer/Thms.lean)

The native writer is opt-in. IPC-to-Parquet composition, additional
nested shapes, compression and other page profiles are outside this
change.

## Independent native readback

Lean emits a file with mixed nullable lists, an empty middle group,
a Unicode name, and both signed INT32 endpoints. It also emits a
schema-only file and a standalone zero-row framed group. PyArrow
26.0.1 opens and reads each, checking the field type and group
boundaries. Apache Thrift 0.25.0 checks the original footer schema,
count fields, ordered frame extents, run bytes and signed word suffix.
Lean examples also exercise typed refusals for a noncanonical child
name and for group, row, slot, header, body, footer and file bounds.
[Wire observations and byte hashes](../../scripts/parquet-list-writer/observations.txt) · [Pinned dependencies](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Writer.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Writer.Examples
python3 scripts/parquet-list-writer/Oracle.py "$replay" |
  diff -u scripts/parquet-list-writer/observations.txt -
```
