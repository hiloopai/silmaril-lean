# Whole-body Snappy in recursive signed Parquet V1

The recursive signed reader admits Snappy PLAIN Data Page V1 from the
original unindexed column. The schema profile supports INT32/INT64,
required and optional Structs, and canonical three-level LIST with at
most one repeated ancestor per leaf. Native emission uses
UNCOMPRESSED V1. Dictionary and indexed profiles and Snappy-coded
pageless chunks remain outside this reader's scope.
[Pageless profile](parquet-recursive-pageless.md)

A V1 page compresses its entire serialized body, including any
length-prefixed repetition and definition sections. The common PLAIN
V1 header check admits RLE levels and bounds the advertised slots.
The original on-disk body must fit the stored byte cap and match the
frame's compressed size. When present, CRC is checked on those bytes
before expansion. The shared payload decoder enforces the raw body
cap, a single complete Snappy block, and exact decompressed length.
The existing flat V1 splitter then bounds and exhausts each admitted
level block, with zero-width sections omitted. The signed slot decoder
requires exactly one signed word for each present slot and consumes
the full suffix. The final chunk check includes each original page
header in the footer's raw byte count. The existing stored chunk,
page, slot and row limits also apply.
[Pinned V1 body layout and sizes](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L722-L779)
[Pinned CRC and chunk sizes](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L819-L841)
[Footer byte accounting](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L904-L945)

`decodeV1Page_wire` binds the original stored slice and checksum to the
bounded decoded body through the payload relation. The V1 level and
word witnesses partition that decoded body in wire order.
`PageWire.counts` derives the exact slot and row changes from the ready
state. The shared chunk walk retains each original frame, carries live
List state across V1 cuts and accepts a V1 row start after a closed V2
page. A repetition-one slot at a closed boundary fails with its
original slot and page coordinates. The existing row, direct Events
and native IPC proofs carry these witnesses and preserve reached
source failures.
[Snappy V2 profile](parquet-recursive-v2-snappy.md)

## Fixtures and regressions

Pinned PyArrow writes checksummed nested V1 Snappy with two groups,
unequal sibling page cuts, null and empty Lists, null elements, and
signed endpoints. A labeled re-encoding of the existing unindexed
mid-row fixture covers a live List crossing two compressed V1 pages.
A second labeled edit inserts an admitted closed V2 to V1 boundary.
The oracle independently examines Compact headers, stored CRC, decoded
body bytes, level sections and signed words. PyArrow reads the three
actual Lean IPC streams, and raw framing confirms their exact EOS.
A labeled late malformed source preserves the completed group and the
first addressed error through empty projection and ahead of writer
admission. Additional controls cover compressed and raw caps, bad
stored CRC, CRC over the decoded body, malformed, short and trailing
blocks, exact signed suffixes, page slots, footer extent, and an
invalid continuation after closed V2.
[Fixture pins](../../scripts/parquet-recursive-v1-snappy-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-v1-snappy-oracle/Axioms.lean
python3 scripts/parquet-recursive-v1-snappy-oracle/check.py
```
