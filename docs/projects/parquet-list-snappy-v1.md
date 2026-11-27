# Opt-in Snappy V1 Parquet LIST to native Arrow IPC

`Parquet.ListFile.Multi.Snappy.convert` accepts the checked canonical
three-level LIST schema with nullable lists and nullable signed INT32
children. The original footer supplies the names, group ordinal, physical
column zero, and full path. Each chunk must advertise Snappy, with PLAIN
values and RLE Hybrid repetition and definition levels in Data Page V1.
The group framer selects the exact original chunk and frames it on the same
immutable source using `Checked.frameGroupFor 1`. The existing uncompressed
entry points still select codec zero.
[Canonical schema and wire evidence](parquet-list-file.md) · [Pinned Parquet format](arrow-parquet-coverage.md)

For each frame the converter checks header admission and the remaining
slot and expansion allowances, then checks the stored payload against its
advertised span and CRC. An absent CRC is accepted. A present CRC is
verified over the complete stored payload using the original i32 bit
pattern. CRC failure returns the checksum error before Snappy dispatch.
The Snappy reader consumes one exact raw member with the header's
advertised expanded size. In V1 this expands both original length-prefixed
level sections together with the PLAIN value suffix. The existing LIST
event decoder consumes this exact expanded body.
[Stored checksum](parquet-page-crc32.md) · [V1 layout and transition rules](parquet-list-v1.md)

The limits cap stored bytes per page, expanded bytes per page, and
cumulative expanded body bytes across the complete file. Expanded byte
accounting includes levels and values. Existing file, framing, row and
slot budgets still apply. Each group starts with an empty continuation
state. A later frame may continue an open list. A group-leading
continuation or a continuation in a chunk with an OffsetIndex is refused.
Slots and rows must match their separate footer counts before the group
contributes a native Arrow batch.
[Existing continuation and OffsetIndex policy](parquet-list-continuation.md)

`readFrame_wire` gives the original stored slice, successful checksum
verification, Snappy denotation and level/PLAIN witnesses for the expanded
body. `readFrames_wire` accounts for exact slot and expanded byte totals
and proves that the concatenated events feed the same continuation state.
`readGroup_wire` ties this to the original footer and shows that those
events reconstruct the exact ordered nullable group rows.

Group admission frames the complete chunk before its body walk. This
preserves the existing typed group framing failure. Once framing succeeds,
the first failed body or transition carries the original page ordinal and
absolute header offset. `readFrames_append`, `readFrames_read_error` and
`readFrames_feed_error` preserve the first such error after a successful
page prefix. `convert_first_error` retains the preceding complete groups
and the original failure, before any native IPC admission. The error
branch has no IPC carrier. `convert_readback` connects the precise
Parquet group witnesses to the native IPC field, ordered batches, nested
nullable rows and exact EOS.
[Public theorem headers](../../Silmaril/Formats/Parquet/ListFile/Multi/Snappy/Thms.lean)

This opt-in path supports Snappy PLAIN V1 only. Dictionary pages,
V2, other codecs, and other nested shapes are outside the profile.

## Independent reproduction

PyArrow 26.0.1 generates two native files, with and without page CRCs.
Each has two groups and four Snappy V1 pages per group. One page compresses
41 bytes to 21 and carries repeated signed INT32 minima. The separately
assembled continuation control rewrites the first repetition value of the
last page of the second group, recompresses that payload, recalculates CRC,
and corrects the framed extents and footer row totals using Thrift.
PyArrow independently checks both the assembled Parquet and the Lean
IPC output. Thrift 0.25.0, zlib and PyArrow's Snappy decoder independently
check framing, CRCs, level bytes and signed PLAIN words. The controls
include a late stored-byte mutation, a malformed Snappy member with valid
CRC, a forbidden group-leading continuation and an exhausted cumulative
byte allowance. Each retains the first group even under a rejecting
IPC row budget.
[Pin and wire references](arrow-parquet-coverage.md) · [Exact hashes and observations](../../scripts/parquet-list-snappy-v1/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Examples
python3 scripts/parquet-list-snappy-v1/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-v1/observations.txt -
```
