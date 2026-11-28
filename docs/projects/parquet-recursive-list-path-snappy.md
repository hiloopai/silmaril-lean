# Snappy PLAIN pages for a canonical signed LIST path

ListPath admits Snappy codec 1 for an unindexed PLAIN column with one
signed INT32 or INT64 leaf under a canonical LIST chain. The checked
binding selects the codec separately for each original column chunk.
The same native Rows, Events and IPC routes read both page versions.
Dictionary pages, additional codecs, indexes and pageless groups remain
outside this profile. [V1 reader](parquet-recursive-list-path-v1.md) · [V2 reader](parquet-recursive-list-path-v2.md)

The shared repeated-leaf payload checks verify optional CRC over the
original stored frame and bound both stored and decoded extents. In V1
the whole original body enters the Snappy decoder, and both prefixed
level sections and the exact signed suffix come from the complete
decoded body. The original frame still carries absolute file offsets.
The section coordinates are tagged as decoded-body-relative for
Snappy V1 and as original file coordinates for UNCOMPRESSED V1 and
all admitted V2 pages.

V2 preserves both original raw Hybrid level sections. The original
true flag selects Snappy for only the stored value suffix, and the
false flag passes that suffix directly to the exact signed-word
decoder. The reader retains V2 row and null counter checks and closes
the ancestry cursor at both V2 boundaries. V1 retains legal
continuation of live ancestors. Both footer totals include the
original serialized page headers.

## Wire and refusal guarantees

The per-page proofs bind both the codec and original stored extent to
the exact decoded levels and signed words. The chunk proof retains the
complete original frame chain, absolute headers and footer totals.
Successful group reconstruction uses the exact ordered trace and row
count. The page refusal proof binds the failure to the next original
frame after a checked prefix, with its original group, path, page
ordinal, header offset and ancestry cursor. Events retain completed
earlier groups under either projection. Source failures precede IPC
output limits. [Events](parquet-recursive-list-path-events.md) · [Arrow V5 IPC](parquet-recursive-list-path-to-ipc.md)

## Verification

Pinned PyArrow and independent Compact, Snappy, Hybrid, CRC and
signed-word checks verify 20 sources and 118 original frames at
depths 3, 4, 6 and 16. Genuine Snappy V1 and V2 sources cover both
signed widths and multiple pages per group. PyArrow supplies 28
false-flag raw V2 suffixes, including eight with signed words.
A labeled reframe independently checks a nonempty raw suffix.
Authored mixed pages exercise V1 continuations at repetitions one,
two and three and both V2 boundaries. The mixed-codec file binds its
original identity and Snappy row groups separately.

Forty Lean IPC streams reach exact EOS under full-field and empty
selection. Nineteen typed controls cover stored CRC, malformed and
trailing Snappy input, exact signed and decoded extents, stored and
decoded byte caps, boundaries and both footer sizes. Late V1 and V2
CRC and codec failures retain the first complete group and original
page address through empty projection and exhausted IPC limits.
[Producer and fixture pins](../../scripts/parquet-recursive-list-path-snappy-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-snappy-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-snappy-oracle/check.py
~~~
