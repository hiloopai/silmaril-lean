# Checked signed V1 chunks beneath two canonical LISTs

This reader binds a strict Parquet snapshot with one top-level
`list<list<signed INT32 or INT64>>` field. It checks the original LIST
annotations, repeated `list` wrappers, signed physical leaf and declared
nullability in their flattened order. It uses the existing LIST context
to compute both empty-wrapper levels and the maximum definition. The
baseline reads unindexed UNCOMPRESSED PLAIN V1. The same entry point
also reads V2 and mixed chunks with a checked column codec.
The entry point returns
original page frames, classified slots, aligned signed words and a
terminal cursor. Rows, Events, IPC and the writer retain their existing
profiles.
[V2 and mixed chunks](parquet-recursive-two-list-v2.md) · [Column codecs](parquet-recursive-two-list-codecs.md) · [One-LIST reader](parquet-recursive-repeated-chunk.md) · [Pinned Parquet nested encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding)

For three optional sites the ordered definitions are:

| Definition | Meaning | Live List after the slot |
| --- | --- | --- |
| 0 | Null outer list | Closed |
| 1 | Empty outer list | Closed |
| 2 | Null inner list | Outer |
| 3 | Empty inner list | Outer |
| 4 | Null signed value | Inner |
| 5 | Present signed value | Inner |

A required declaration contributes no null step. Each repeated wrapper
contributes its empty step, so required variants still distinguish both
empty lists. The proof identifies the exact step for each original
wrapper and the unique definition for each admitted event.

Repetition zero starts a row. Repetition one starts a new inner element
and requires a live outer list in the incoming cursor and the current
definition. Repetition two continues the inner list and requires both
wrappers on both sides. The next cursor derives its live depth solely
from the current slot. A null or empty inner list closes any previous
inner list. A null or empty outer list closes both.

Each V1 page checks the original header, optional stored CRC, two
length-prefixed Hybrid sections and exact PLAIN suffix. The chunk reader
scans the bounded original frame chain, then feeds the outgoing cursor
of each page directly into the next body, starting closed at the
original group boundary. Body failures retain the frame ordinal,
original byte address and incoming cursor. The checked span and the
independent footer slot and row counts must agree at completion.
The page, body, level, chunk, slot and row limits bound this path.

## Fixtures and regressions

Pinned PyArrow generates both signed widths, all eight nullability
combinations and the fully optional declaration at each width.
Independent Compact, Hybrid and signed-word inspection compares
the exact level and value traces to PyArrow’s decoded rows. A labeled
reframing of one original group starts pages at repetition one and
two, including after null and empty inner lists and after a null leaf.
Typed controls cover stale and unreached ancestors, out-of-range
levels, trailing level or scalar data, CRC, footer totals, limits and
out-of-profile codecs and indexes. The old one-LIST entry point
continues to refuse this nested shape.
[Producer and fixture pins](../../scripts/parquet-recursive-two-list-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-oracle/check.py
~~~
