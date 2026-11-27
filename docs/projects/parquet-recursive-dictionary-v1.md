# Dictionary-first V1 in recursive signed Parquet

The recursive reader admits unindexed, UNCOMPRESSED Data Page V1
columns with one leading PLAIN DictionaryPage and RLE_DICTIONARY
data pages. A file can have both dictionary and PLAIN columns.
The schema admits signed INT32 and INT64 leaves, Structs and
canonical three-level LIST with at most one repeated ancestor per
leaf. PLAIN_DICTIONARY, dictionary V2, compressed dictionaries
and dictionary-to-PLAIN fallback are outside this slice.
[Dictionary V2 extension](parquet-recursive-dictionary-v2.md) · [PLAIN fallback](parquet-recursive-dictionary-fallback.md) · [Snappy](parquet-recursive-dictionary-snappy.md)
[Parquet encoding specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)

The positional column binding retains the original physical path,
type, codec and checked chunk span. The dictionary consumes physical
page ordinal zero and occupies the original range from the declared
dictionary offset through the declared first data-page offset. It
contributes zero slots and rows. The original frame parser checks
its bounds. The checksum reader checks the optional stored-body
CRC, and the signed PLAIN reader exhausts exactly the declared
number of dictionary words. Each data page uses only the entries
from that column's leading frame. A later dictionary is an indexed
page failure.

The V1 level reader supplies the exact repetition and definition
words and the existing List cursor supplies the live continuation
state. Only present slots consume indices. A width octet precedes
the Hybrid stream, which must exhaust its original suffix. The
final packed run may contribute up to seven ignored positions.
An all-null page can carry width zero with no runs, including
when the dictionary has zero entries. Ordered lookups bind each
consumed index to an in-range original signed word. Entry, dictionary
byte, index byte and index count caps supplement the existing page,
body, chunk, slot and row bounds. The dictionary counts toward the
physical page cap and header-inclusive footer lengths.
[Parquet dictionary and page headers](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

Rows, direct Arrow Events and native IPC consume the same checked
chunk observations. The original page ordinal, byte offset and
incoming slot and row state identify a reached page failure. Empty
projection preserves every completed group and the original
terminal failure. Native IPC validates the original source before
applying its writer limits. Existing PLAIN profiles, pageless group
admission and native writer behavior retain their contracts.

## Fixtures and regressions

The oracle uses genuine PyArrow nested V1 files with the producer's
default dictionary selection and with mixed PLAIN and dictionary
columns. The admitted fixtures include both signed widths and their
endpoints, an empty dictionary, null and empty lists, null elements,
and nullable Struct descendants. A labeled edit re-encodes the
previously checked unindexed mid-row split with packed indices and
final padding. Independent Compact and Hybrid inspection checks
original frame order, offsets, CRCs, entries, levels and index
traces against PyArrow logical values. PyArrow reads the emitted
Lean Arrow streams, and independent IPC framing checks exact EOS.

The controls exercise missing and repeated dictionaries, misordering,
both original offsets, index bounds and exact extent, CRC, entry and
byte caps, and header-inclusive footer totals. A genuine Zstandard dictionary file
exercises the codec boundary. A late original index
failure preserves the earlier group through empty projection and
takes precedence over native output limits.
[Fixture pins](../../scripts/parquet-recursive-dictionary-v1-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-v1-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-v1-oracle/check.py
~~~
