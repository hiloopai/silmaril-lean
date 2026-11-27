# Selected GZIP DATE dictionaries with V2 data pages

`Parquet.Date.Leaf.Dictionary.Gzip.V2` is an opt-in source for a selected
flat INT32 DATE leaf. It uses the original checked snapshot, schema binding,
column span and exact footer offsets. Each admitted group contains a
leading PLAIN dictionary and a nonempty sequence of V2 RLE_DICTIONARY data
pages. Planning locates the first unsupported original frame, so a PLAIN
transition and any subsequent dictionary reentry fail at the first PLAIN
page's ordinal and header offset. V2 data parameters come from the original
header and the layout of the selected leaf.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Gzip/V2/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Gzip/V2/Thms.lean)

The dictionary uses the existing whole-body GZIP member check and exact
signed PLAIN INT32 decode. Shared V2 preparation accounts for the original
stored CRC, raw levels and the suffix selected by the compression flag.
Compressed suffixes contain exactly one bounded GZIP member. Raw suffixes
retain their original bytes. The required or nullable definition mask and
checked Hybrid indices account for every signed optional day, with exact
row and null counts. The existing chunk limits bound total stored bytes,
declared expansion and rows independently.
[Parquet page headers](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Parquet encoding rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8)

Native Date32 readback retains the exact field name, nullability, and
ordered groups through EOS. A late failure retains complete earlier groups
and the original indexed cause. A framed page failure has its original
absolute header offset. A failure during framing keeps the original group
index and typed framing cause. Source failure takes precedence over IPC
writer checks.

## Independent comparison

Pinned PyArrow writes three genuine dictionary-only files, including a
required leaf without CRC and nullable files exercising each compression
flag with signed endpoints. Thrift and zlib verify the original frames,
dictionary entries, stored CRCs, raw levels, and suffix encodings. PyArrow
also reads back the emitted Date32 IPC. The negative cases include a genuine
late fallback, a header mutation introducing reentry after that first PLAIN
page, an independently rewritten out-of-range index with a valid stored
CRC, and an assembled second GZIP suffix member.
[Comparator](../../scripts/parquet-date-gzip-dictionary-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-dictionary-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-dictionary-v2/Axioms.lean
python3 -I scripts/parquet-date-gzip-dictionary-v2-oracle/check.py
```
