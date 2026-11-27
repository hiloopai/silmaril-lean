# Selected GZIP DATE dictionaries with V1 data pages

`Parquet.Date.Leaf.Dictionary.Gzip.V1` is an opt-in source for a selected
flat INT32 DATE leaf. Each group contains a leading PLAIN dictionary and a
nonempty sequence of V1 RLE_DICTIONARY pages. The checked DATE binding and
chunk selector retain the original footer group, column path, chunk span,
and frame chain. Header planning reports the first unsupported framed page
at its original ordinal and header offset. A PLAIN transition with later
dictionary reentry fails at the first PLAIN page.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Gzip/V1/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Gzip/V1/Thms.lean)

The leading dictionary uses the existing whole-body GZIP member and signed
PLAIN INT32 checks. Each original V1 reference page validates the entire
stored body and its CRC when present. One exact bounded GZIP member supplies
both the levels and reference bytes. The shared V1 preparation law links
those bytes to the selected required or nullable layout, checked mask and
ordered Hybrid indices. The indices resolve to exact signed dictionary
entries, and the slots account for every declared group row. Stored page and
chunk extent, expanded sizes, and row and index limits are checked independently.
[Shared V1 preparation law](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/Thms.lean) ·
[Parquet page headers](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

Native Date32 readback preserves the selected field name and nullability
and one ordered batch per original footer group through exact EOS. A late
failure retains the earlier complete groups and the original index and
cause. A framed page failure carries the original header offset. A
framing failure carries its typed cause and group index. Source errors take
precedence over IPC writer checks.

## Independent comparison

Pinned PyArrow emits nullable CRC-bearing and required CRC-absent
dictionary-only V1 files, with multiple groups and signed endpoints.
Thrift and zlib compare the original frames and verify CRCs, the full
GZIP members, the required or nullable masks, and exact dictionary
lookups. PyArrow independently reads back the Lean-emitted IPC.
Controls include genuine late PLAIN fallback, an explicitly labeled
reentry mutation, wrong level encoding, a valid outer CRC with an invalid
GZIP trailer, a second member assembled at the final reference page, and
a genuine V2-only dictionary file.
[Comparator](../../scripts/parquet-date-gzip-dictionary-v1-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-dictionary-v1-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-dictionary-v1/Axioms.lean
python3 -I scripts/parquet-date-gzip-dictionary-v1-oracle/check.py
```
