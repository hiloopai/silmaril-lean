# LZ4_RAW in recursive signed Parquet dictionary chunks

The unindexed recursive signed INT32/INT64 Struct/LIST reader admits
the following codecs for a column with one original leading PLAIN
dictionary. V1 and V2 data pages select RLE_DICTIONARY or PLAIN by
their original encoding tag, including fallback within a chunk.

| Original codec ID | Dictionary and V1 | V2 value suffix with resolved flag true |
| --- | --- | --- |
| 0 UNCOMPRESSED | Raw body | Raw suffix |
| 1 SNAPPY | Exact raw Snappy block | Exact raw Snappy block |
| 2 GZIP | One bounded GZIP member | One bounded GZIP member |
| 4 BROTLI, opt-in | One bounded raw-meta-block stream | One bounded raw-meta-block stream |
| 6 ZSTD | One bounded dictionary-free Zstd frame | One bounded dictionary-free Zstd frame |
| 7 LZ4_RAW | Exact raw LZ4 block | Exact raw LZ4 block |

V2 repetition and definition spans remain raw. A false V2 flag uses
the original raw suffix directly and bypasses the codec. Codec ID 5
is a typed column refusal. The checked codec 7 adapter uses the raw
block format and refuses an LZ4 frame in the original dictionary body.
[GZIP bounds](parquet-recursive-dictionary-gzip.md) · [Zstd bounds](parquet-recursive-dictionary-zstd.md) · [Raw Brotli opt-in](parquet-recursive-dictionary-brotli-raw.md) · [Pinned Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

The dictionary codec table agrees with the column table for every
admitted codec. The binding proof connects the dictionary decoder
directly to the original positional column. The existing wire
relations check the original stored CRC, stored and decoded bounds
and exact decoded bytes. Hybrid checks the variable index extent,
and every present slot selects from the same column's original
ordered dictionary. PLAIN pages consume their exact signed words.
The chunk proof retains header-inclusive stored and decoded totals,
including the dictionary, and the page, row and slot counts.
V1 carries its live List cursor across pages. V2 closes it at
the row boundary.
[Pinned V2 header and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

## Fixtures and regressions

Pinned PyArrow writes genuine codec-7 nested signed V1 and V2,
with dictionary-to-PLAIN fallback in both versions. V2 includes
genuine raw and compressed index suffixes and PLAIN fallback
suffixes. One labeled edit changes an original compressed V2
index suffix to raw while preserving the exact levels and indices.
Another re-encodes the checked V1 mid-row continuation into PLAIN
using the pinned liblz4 block writer.

The independent liblz4 decoder, Compact and Hybrid inspection,
and PyArrow verify original frame spans, stored CRCs, signed words,
index order and both footer totals. PyArrow reads Lean's native
IPC streams, and independent framing verifies exact EOS. Controls
exercise deprecated ID 5, framed LZ4, trailing input, wrong
decoded extents, checksum failures and caps. Late V1 and V2 index
errors retain the completed group and original address through
empty projection and take precedence over native IPC output limits.
[PyArrow and liblz4 fixture pins](../../scripts/parquet-recursive-dictionary-lz4-raw-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-lz4-raw-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-lz4-raw-oracle/check.py
~~~
