# Snappy data pages beneath two canonical LISTs

The Snappy extension adds codec 1 to the identity profile for unindexed
PLAIN V1/V2 chunks with a single signed INT32 or INT64 leaf. The compiled
LIST thresholds still distinguish null lists, empty lists and null leaf
values. The column codec is part of every page witness in the same
ordered chunk. The checked profile excludes dictionary pages and indexes.
[Current codec matrix](parquet-recursive-two-list-codecs.md) · [Two-LIST schema and cursor](parquet-recursive-two-list.md) · [V2 counts and boundaries](parquet-recursive-two-list-v2.md)

V1 verifies the original stored frame and optional page CRC, then passes
the whole body to the shared bounded Snappy adapter. The checked
length-prefixed repetition and definition streams and signed words
come from that exact decoded body. V2 verifies the original stored CRC
before splitting the body at the original header lengths. Both counted
Hybrid level slices remain raw. A true resolved flag sends only the
stored value suffix to the codec. A false flag uses the original raw
suffix directly. The wire witnesses retain the original slices and the
shared payload denotation, including full consumption of the Snappy
block and the exact decoded extent.

Both stored and decoded page lengths are bounded. For V2, the raw level
bytes count against the page cap and the compressed suffix must expand
to the signed extent declared by the original slot and null counts.
The cursor checks those counts against the decoded slots, including
repetition-zero row starts. Both footer byte totals include each
original serialized header, with the compressed size on the stored side
and the decoded size on the raw side.

V1 keeps its live inner and outer ancestry across page boundaries.
V2 starts a new row and closes its cursor, including in mixed chunks.
The existing Rows, Events and IPC entry points use these observations.
Direct Events reports the original addressed page failure and completed
group prefix under both selections. A source failure takes precedence
over IPC output limits.
[Event projection](parquet-recursive-two-list-events.md) · [IPC readback](parquet-recursive-two-list-to-ipc.md)

## Reproduction

Pinned PyArrow emits genuine Snappy V1 and V2 positives at both signed
widths with required and nullable shapes and multiple groups and pages.
The independent Compact, Hybrid, signed-word and raw Snappy inspection
checks the stored CRC, exact byte extents and both footer totals.
It compares the independently expanded bytes with Lean and checks
PyArrow readback of the emitted IPC through exact EOS.

Labeled edits exercise both V1 continuation depths, legal mixed
transitions, and replacing a compressed V2 suffix with its original raw
values under a false flag. Typed controls separate stored CRC from the
codec stream, stored and decoded caps, malformed and trailing Snappy,
signed extents, invalid levels, boundary rules and both footer totals.
Late CRC and codec failures retain the earlier group and original
address through empty projection and ahead of exhausted IPC limits.
[Producer, source and IPC pins](../../scripts/parquet-recursive-two-list-snappy-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-snappy-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-snappy-oracle/check.py
~~~
