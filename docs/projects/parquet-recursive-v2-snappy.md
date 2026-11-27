# Snappy suffixes in recursive signed Parquet V2

The checked recursive reader admits Snappy on unindexed PLAIN Data
Page V2 columns with signed INT32/INT64 leaves. The required and optional
Struct and canonical three-level LIST profile still permits at most
one repeated ancestor per leaf. Native emission uses UNCOMPRESSED V1.
A reached V1 page requires the UNCOMPRESSED column codec. The source
continues to refuse dictionaries and indexes.

The original footer supplies the column codec. The original V2 header
resolves `is_compressed`, which defaults to true. A false flag takes
the original value suffix verbatim, including under a Snappy column
codec. The decoder verifies CRC on the original stored body, then
reads the raw repetition and definition spans with the existing V2
hybrid readers. The compressed and uncompressed sizes must both cover
the level prefix. On the Snappy path the header's remaining
uncompressed size must fit the body limit and equal the signed word
width times the header's non-null count before decompression. The
shared payload reader requires one complete raw Snappy block and exact
input and output lengths. The shared signed slot reader separately
checks the classified value positions, row starts, nulls and V2 row
boundary. At chunk exhaustion, the footer's uncompressed size must
equal the sum of the original header lengths and advertised raw page
body lengths for a Snappy column. The stored byte, page, slot and row
limits apply to the same original chunk walk.
[Pinned V2 header and flag semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)
[Pinned chunk size semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L904-L945)

`readV2Suffix_wire` certifies both header subtractions and the selected
codec relation. `decodeV2Page_wire` links that witness to the three
original source spans and the stored-body checksum. Its accounting law
gives the exact decoded word extent, slot and row totals, and the
closed V2 boundary. The existing chunk and group witnesses carry these
laws into Rows, direct Events and native Arrow IPC. Terminal group
errors retain the reached original column, page, byte and state.

PyArrow 26.0.1 records codec 1 on the empty chunks of a Snappy pageless
group, while its group counts, chunk size and page-offset placeholders
remain zero. The recursive pageless policy admits codec 0 only, so this
form receives the strict footer interval refusal. The existing
UNCOMPRESSED pageless and framed zero groups remain covered.
[Pageless profile](parquet-recursive-pageless.md)

## Fixtures and regressions

Pinned PyArrow generates a nested all-Snappy V2 file and a nested V2
file with Snappy on only two physical leaves. The all-Snappy file
contains both flag values. A labeled header edit omits the true flag to
exercise its default. Independent Thrift, CRC, hybrid and Snappy
inspection checks the absolute spans and signed words against Lean on
all three files. Pinned PyArrow reads the three actual Lean IPC streams
with the original group counts and nested values. Raw IPC inspection
checks exact EOS. Labeled controls cover a late malformed block,
trailing bytes, incorrect decoded extent, incorrect stored CRC,
CRC computed over the decoded body, extent arithmetic, cumulative
metadata size and stored and decoded body limits. Direct Events
preserves the completed group and terminal cause through empty
projection. The native IPC route returns the same original failure
ahead of writer limits. Genuine Snappy V1, Gzip V2 and Snappy pageless
sources exercise the profile refusals.
[Fixture pins](../../scripts/parquet-recursive-v2-snappy-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-v2-snappy-oracle/Axioms.lean
python3 scripts/parquet-recursive-v2-snappy-oracle/check.py
```
