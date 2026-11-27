# Bounded GZIP in recursive signed Parquet dictionary chunks

The unindexed recursive signed INT32/INT64 Struct/LIST reader
admits codec 2 in a column with one original leading PLAIN
dictionary. Each original data page chooses RLE_DICTIONARY or
PLAIN fallback by its encoding tag. The dictionary and column
codec tables agree, so the original positional binding supplies
the codec for the dictionary and every subsequent page.
[Support matrix](parquet-recursive-dictionary-lz4-raw.md) · [Pinned Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

The existing GZIP adapter reads exactly one bounded RFC 1952 member
with a checked trailer CRC and ISIZE. Its controller-call budget
is independent of the stored and decoded byte caps. The default
budget is 65,536 calls per reached member. The Parquet page CRC
covers the entire original stored body. The original dictionary
and V1 data pages expand the whole body.

V2 retains the original raw repetition and definition spans. A
true resolved flag expands only the original value suffix. A
false flag uses the original raw suffix and consumes zero GZIP
calls. The header supplies the exact stored and decoded extents.
Hybrid exhausts the variable-length index suffix and every present
slot refers to the same column's ordered dictionary. PLAIN fallback
checks the exact signed-word extent.
[Pinned V2 header and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

The original frame chain counts the dictionary in the page cap and
both header-inclusive footer byte totals. The dictionary contributes
zero data slots and row starts. V1 carries the live List state
across its page boundaries, including at encoding changes. V2
requires a row start and closes the boundary for either encoding.
Direct Events and native IPC share the same addressed chunk reader.

## Fixtures and regressions

Pinned PyArrow emits codec-2 nested V1 and V2 with per-page PLAIN
fallback. The V2 fixtures include genuine raw and compressed index
and PLAIN suffixes. An authored raw bypass retains the levels and
decoded indices of an original compressed V2 page. A second
authored fixture keeps a V1 mid-row continuation into PLAIN.
Independent bounded zlib inspection checks single-member completion,
exact consumption, CRC and ISIZE. Compact and Hybrid inspection
checks original frame offsets, dictionary entries, index order,
signed words and both footer totals. PyArrow and raw IPC framing
verify the native output through exact EOS.

The controls distinguish the Parquet stored CRC from the GZIP
member CRC and ISIZE. Trailing bytes and a second complete empty
member are refused. Additional controls check raw extent, separate
byte and controller caps, page budget and footer totals. The
zero-call tests first obtain the checked dictionary, then verify
the raw V2 index and PLAIN pages and the exhaustion of compressed
pages. Late index and GZIP trailer failures retain the completed
group and original address through empty projection and take
precedence over native IPC output limits.
[PyArrow, zlib and fixture pins](../../scripts/parquet-recursive-dictionary-gzip-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-gzip-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-gzip-oracle/check.py
~~~
