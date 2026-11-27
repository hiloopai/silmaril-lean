# Selected GZIP DATE fallback into native Date32 IPC

`Parquet.Date.Leaf.Fallback.Gzip` reads a selected flat, annotated INT32 DATE
leaf by physical ordinal. The existing DATE binding and chunk selector verify
the original schema, column path and footer spans in one checked snapshot.
Each group has one leading PLAIN dictionary and V1 data pages with a nonempty
RLE_DICTIONARY prefix and a nonempty PLAIN suffix.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/Thms.lean)

Planning checks the stored chunk extent and cumulative declared expansion
before reading page bodies. It retains original frame order and declared
dictionary and data offsets. If an admitted prefix already contains an encoding
transition error, the earlier frame takes precedence over a later unsupported
header. Body decoding starts after the whole group's plan succeeds.

Each dictionary or data frame verifies its original stored extent and CRC
when present. The entire stored V1 body expands as exactly one bounded GZIP
member. The dictionary contains signed little-endian INT32 words. Data pages
reconstruct the checked definition mask with either ordered references into
those entries or the PLAIN words in the original scalar slice. The row cap,
dictionary limits, stored and expanded page and chunk limits, level and index
limits, and GZIP controller call limit remain independent.
[Parquet encoding specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8) ·
[Parquet GZIP specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#gzip)

The event source keeps complete earlier groups and reports the original
footer group index on failure. The dictionary is page zero and data page
errors include their original ordinal and absolute header offset. Successful
IPC readback preserves the exact field name and nullability and one ordered
batch of signed nullable days per original footer group through EOS. Source
errors precede sink checks. This profile admits V1 only. The existing PLAIN,
Snappy, and default readers keep their original admission rules.

## Independent comparison

The pinned PyArrow producer emits both a nullable CRC-bearing file and a
required file without page CRCs. The DATE leaf is second beside an unannotated
INT32. Thrift and zlib verify exact frames, both checksums, signed endpoints,
definition levels and both encoding phases before PyArrow compares the
Lean-emitted IPC descriptor and batches. Controls include genuine V2 and
dictionary-only sources, malformed Thrift tags and CRCs, low caller limits,
and a deliberately assembled page with a second GZIP member. Late controls
check that the first group's batches survive and the original source error
wins against a zero-batch sink budget.
[Oracle](../../scripts/parquet-date-gzip-fallback-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-fallback-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-fallback/Axioms.lean
python3 -I scripts/parquet-date-gzip-fallback-oracle/check.py
```
