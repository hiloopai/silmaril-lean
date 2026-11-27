# Checked Zstandard in recursive signed Parquet V1 and V2

The recursive reader admits Parquet codec 6 for unindexed PLAIN
Data Page V1 and V2, with signed INT32/INT64, Struct and canonical
three-level LIST and at most one repeated ancestor per leaf.
The reader uses the checked Zstd adapter already used by the
TIMESTAMP routes. The recursive pageless profile requires codec zero
and native emission uses UNCOMPRESSED V1.
[Pinned Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

The adapter reads one standard dictionary-free frame and exhausts it.
Its supported blocks are raw, RLE and checked compressed blocks.
The compressed path uses raw and RLE literals or checked Huffman
tables, including one- and four-stream literals and treeless blocks
with an established table. Sequence decoding supports predefined,
RLE, transmitted FSE and checked repeat tables. Match execution
uses the strict RFC window rule. Nonzero dictionary IDs, skippable
frames, reserved headers or blocks, invalid tables and unmatched
input produce typed frame errors. When present, the frame content
size and content checksum are checked against the decoded bytes.

`Chunk.Limits.zstd` defaults to an 8 MiB window and 43,690 commands
per block, matching the timestamp adapter. Each block fits the
frame's block maximum and sees the remaining output budget. The
input byte count bounds the block walk, and the adapter bounds
Huffman table descriptions to 128 bytes, 256 symbols and depth 11.
The Parquet stored and decoded byte caps also apply independently.
[Zstandard frame and block specification](https://www.rfc-editor.org/rfc/rfc8878.html#section-3.1)

V1 expands the original whole body after checking optional Parquet
CRC over the stored bytes. V2 retains the original raw level spans
and expands the stored value suffix only when its resolved flag
selects the column codec. A false flag uses the original raw suffix.
The recursive wire witness uses the checked adapter's frame witness
for Zstd and the existing payload denotation for the other codecs.
Both paths bind the exact decoded extent and signed slots to the
original frame. The chunk proof retains header-inclusive footer
accounting and the existing row, null and continuation laws.
[Pinned V2 header and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

## Fixtures and regressions

Pinned PyArrow writes genuine codec-6 nested V1 and V2 files with
checksums, unequal sibling page cuts, null and empty Lists, null
elements and signed endpoints. The genuine V2 file includes raw
suffixes. Pinned libzstd independently inspects the frame boundaries,
headers and decoded bytes. Compact and level inspection checks the
stored CRC, page positions, counts and signed values. Two labeled
fixtures replace a native block with a separately generated
content-checksummed frame and recompute the stored Parquet CRC.
PyArrow and raw IPC inspection verify the resulting Lean streams
through exact EOS.

Labeled controls exercise nonzero dictionary IDs, oversized blocks,
truncation, content size, separate stored and content checksums,
window and command limits, both byte caps, extra bytes and a second
frame, and header-inclusive footer totals. The reached content
checksum failure preserves the completed group and original
coordinates through empty projection and ahead of IPC writer limits.
A genuine codec-6 pageless group exercises the strict footer refusal.
[Fixture and libzstd pins](../../scripts/parquet-recursive-zstd-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-zstd-oracle/Axioms.lean
python3 scripts/parquet-recursive-zstd-oracle/check.py
```
