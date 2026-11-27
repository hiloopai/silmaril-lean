# Selected PLAIN V1 Parquet DATE with Zstandard

`Parquet.Date.Leaf.Zstd` binds one physical ordinal in the existing
strict checked flat DATE snapshot. The leaf must be INT32 and have an
admitted DATE annotation. The new reader shares the PLAIN chunk planner
with the GZIP DATE reader. It selects codec 6 and checks V1 PLAIN page
headers, the original chunk span and page offsets, the footer row count,
and independent stored and expansion budgets. It accepts optional
Parquet page CRCs and verifies each present CRC on the stored bytes
before decoding that page. The existing GZIP and default readers retain
their profile checks.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Zstd/Defs.lean) ·
[DATE binding](parquet-date-selected-leaf.md)

The selected page decoder uses the existing flat INT32 Zstandard
decoder and the checked RFC 8878 frame contract. The entire original
V1 payload is one dictionary-free frame. The original size and CRC,
exact block chain and trailer, window and expansion bounds, and
regenerated V1 level and PLAIN scalar slices are part of the witness.
The same signed words and presence mask recover the nullable slots in
wire order. This profile uses the strict checked decoder's
`distance < Window_Size` condition. Page V2 and dictionary pages are
outside this entry point.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Zstd/Thms.lean) ·
[Flat INT32 Zstandard](parquet-flat-zstd.md) ·
[Checked Huffman frames](zstd-huffman-frame.md)

A completed DATE source emits native Date32 IPC with the exact field
name and nullability and one batch per footer group, in order through
EOS. A page decode failure keeps its page ordinal and original header
offset. At the stream boundary the first failing group keeps its
complete earlier event prefix and its typed cause takes precedence over
IPC writer limits.

## Pinned comparison

Three genuine PyArrow 26.0.1 files use level 3 Zstandard, with the DATE
leaf following a separate unannotated INT32 column. The fixtures cover
required and nullable fields, both signed Int32 endpoints, CRC-bearing
and CRC-absent pages, and raw and compressed Zstandard blocks,
including an original Huffman literal block. Thrift checks the raw
footer and page headers, libzstd 1.5.7 checks each exact frame extent,
and zlib checks the stored CRC. PyArrow decompresses the payload and
independently reads the source rows and Lean-emitted IPC.

Labeled mutations exercise a bad stored CRC, bad Zstandard magic with
a recomputed stored CRC, and a valid frame prefix followed by a trailing
byte inside the checked page extent. Separate controls exercise low
stored and expanded caps, the Zstandard window bound, and genuine
V2 and dictionary producer outputs. The late failures use a zero-batch
sink cap and check the complete earlier group.
[Runner](../../scripts/parquet-date-zstd-v1-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-zstd-v1-oracle/fixtures.json) ·
[libzstd 1.5.7](https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Zstd.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Zstd.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-zstd-v1/Axioms.lean
python3 -I scripts/parquet-date-zstd-v1-oracle/check.py
```
