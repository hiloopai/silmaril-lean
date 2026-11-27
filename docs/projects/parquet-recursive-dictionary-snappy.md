# Snappy in recursive signed Parquet dictionary chunks

The unindexed recursive INT32/INT64 Struct/LIST profile admits
UNCOMPRESSED and SNAPPY dictionary-first columns. The original
column codec selects a bounded payload reader for the original
leading PLAIN dictionary and later data pages. Each column uses
only its own ordered dictionary. V1 and V2 data headers select
RLE_DICTIONARY or PLAIN fallback per page.
[Parquet dictionary encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8)

A Snappy dictionary uses one raw block for the whole body. The
reader checks stored CRC and the stored and decoded byte limits,
then checks exact decoded extent and exhausts the ordered signed
words. Snappy V1 likewise expands the whole original data body.
The original V1 levels retain the live List cursor across page
and encoding changes.

V2 repetition and definition sections remain raw. For a true
resolved flag the Snappy decoder gets only the original value
suffix, with its exact stored and decoded lengths derived from the
header. A false flag uses the original suffix directly. The Hybrid
reader exhausts the variable-length index extent and gives one
in-range index per present slot. Compressed PLAIN fallback retains
its fixed signed-word extent check. CRC covers the entire original
stored body before either path. V2 retains its slot, row and null
counts and closed List boundary.
[Pinned V2 header, codec and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

The original frames include the leading dictionary in the page cap
and both header-inclusive footer byte totals. The stored total
follows the exact original span, and the decoded total sums each
original header and validated raw body size. The dictionary
contributes zero data slots and row starts. Rows, direct Events and
native IPC use the same addressed reader. Empty projection
preserves a completed group and the original terminal error.

## Fixtures and regressions

Pinned PyArrow supplies genuine nested files with its default
Snappy and dictionary settings, V1 and V2 fallback with both
signed widths, empty dictionaries, and a V2 repeated column with
compressed indices. The fixtures have genuine raw V2 index
suffixes and both raw and compressed PLAIN fallback. A labeled
raw bypass preserves the levels and decoded index suffix of an
original compressed V2 page. A second authored file re-encodes
the previously checked V1 mid-row switch to PLAIN with Snappy.

Independent Compact, Snappy command, Hybrid and signed-word
inspection checks original spans, CRC, exact payload consumption,
ordered dictionaries and indexed values, and both footer totals.
PyArrow reads the Lean-emitted IPC and independent framing checks
exact EOS. The controls exercise stored CRC, malformed or trailing
Snappy, byte and page caps, raw extents, omitted dictionary bytes
in the decoded total and a short stored total. Late index failures
in both versions occur after successful Snappy decoding and retain
the earlier group through empty projection and ahead of IPC output
limits.
[Fixture pins](../../scripts/parquet-recursive-dictionary-snappy-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-snappy-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-snappy-oracle/check.py
~~~
