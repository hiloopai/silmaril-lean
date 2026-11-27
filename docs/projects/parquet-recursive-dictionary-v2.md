# Dictionary-first V2 in recursive signed Parquet

The recursive signed INT32/INT64 Struct/LIST reader admits
UNCOMPRESSED RLE_DICTIONARY Data Page V2 after the same leading
PLAIN dictionary used by V1. Columns are unindexed, with at most
one repeated ancestor per leaf. Pages select V1 or V2 from the
original frame and require RLE_DICTIONARY in either version.
PLAIN fallback and PLAIN_DICTIONARY are typed encoding refusals.
Compressed dictionaries remain outside this profile.
[Parquet dictionary encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)

The common V2 reader verifies the optional CRC over the original
stored body and takes the original repetition, definition and
index spans from the bounded header. Level sections have no V1
length words, and a zero maximum requires an empty section. For
codec zero, a false, true or omitted is_compressed flag leaves the
suffix raw. Both advertised body sizes must equal the stored extent.
The original index span has a width octet followed by exact Hybrid
runs for the present slots, with the final packed padding rule.
The span length follows the header and Hybrid consumption.
Each returned value is the in-range entry of the same original
ordered dictionary.
[Pinned V2 header and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

V2 starts at repetition zero for a nonempty page. The decoded
levels give the original slot, row-start and null counts, and
V2 closes the List cursor after every page. An empty V2 page
contributes zero slots and rows and still consumes its physical
frame. V1 pages continue an open List across V1 boundaries.
The original chunk walk includes the dictionary and all data
headers in the footer totals. Rows, direct Events and native IPC
use the same checked source and preserve addressed group and
page failures. Empty projection preserves the earlier groups
and terminal outcome. The file writer and pageless policies
retain their existing contracts.

## Fixtures and regressions

Pinned PyArrow supplies genuine nested V2 dictionary columns,
mixed PLAIN and dictionary siblings, empty dictionaries, and
zero-slot data pages inside nonempty groups. Independent Compact
and Hybrid inspection checks footer extents, both raw level
sections, row and null counts, stored CRCs, ordered dictionary
entries and the exact index traces. PyArrow reads the Lean-emitted
IPC, and raw framing checks exact EOS.

Labeled controls cover both forms of the true flag under codec
zero, unequal body sizes, bad level and index extents, slot,
null and row counts, index bounds and caps, CRC, and unsupported
encodings. A mixed-version carrier retains the earlier authored V1 continuation
after the authored V2-to-V1 transition. Two boundary failures
check a V1 continuation after V2 and a V2 page starting inside
a live V1 row. A late malformed index stream retains the earlier
group and its addressed failure through empty projection and
precedes native IPC output limits.
[V2 fixture pins](../../scripts/parquet-recursive-dictionary-v2-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-v2-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-v2-oracle/check.py
~~~
