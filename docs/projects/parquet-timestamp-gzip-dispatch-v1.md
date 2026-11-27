# Per-row-group GZIP V1 Parquet TIMESTAMP dispatch

`Timestamp.Leaf.Gzip.Dispatch.V1.convert` explicitly selects one modern
flat INT64 TIMESTAMP leaf from a checked Parquet snapshot. Each selected
column chunk uses GZIP and starts with one PLAIN dictionary frame.
The existing GZIP V1 dictionary-only and dictionary-to-PLAIN converters
retain their admission rules.

The dispatcher frames the selected chunk once. A PLAIN Data Page V1
header in that original data-frame list selects fallback. Otherwise it
selects dictionary-only. That standalone path checks every original
header, the footer row total, and its page sequence before decoding bodies.
The fallback path requires a nonempty dictionary-data prefix and a
nonempty PLAIN suffix in that order. One branch runs for each row group.

The dispatch theorem equates the entire group result with the selected
standalone result. It covers signed nullable slots and typed failures at
their original page ordinals and absolute offsets. Shared framing errors
have the same cause in all three entry points. The wire laws connect the
retained original frames to the selected branch's checked dictionary and
page witnesses. Those witnesses include the original Parquet page CRC
when present, one exact bounded GZIP member with CRC-32 and ISIZE, and the
original level and value bytes.

Events preserve the earlier complete footer groups when a later group
fails. The first source failure preempts IPC writer admission. Successful
native Arrow V5 readback retains the field name, nullability, tick unit,
UTC or local interpretation, and every signed count through EOS.

## Independent verification

PyArrow 26.0.1 writes both pinned mixed-profile files directly. Their
selected chunks alternate dictionary-only, fallback, and dictionary-only
with original page tags `[8, 8]`, `[8, 0, 0]`, and `[8, 8]`. The files
cover nullable UTC nanos and required local micros, stored CRC present
and absent, distinct dictionaries, and signed extrema. Thrift and zlib
check original frame extents, both integrity layers, definitions,
references, and PLAIN values. PyArrow independently reads the actual
Lean-emitted IPC through EOS.

The separately labeled mutations exercise stale stored CRCs, invalid
member CRCs with recomputed outer CRCs, an invalid footer data offset,
and two page-sequence failures. A two-fault file checks earliest-group
precedence. The comparator checks exact agreement with the chosen
standalone reader on successful groups and on its typed failures.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Gzip/Dispatch/V1/Thms.lean) ·
[Dictionary-only](parquet-timestamp-gzip-dictionary-v1.md) ·
[Fallback](parquet-timestamp-gzip-fallback-v1.md) ·
[Comparator](../../scripts/parquet-timestamp-gzip-dispatch-v1-oracle/check.py) ·
[Pins](../../scripts/parquet-timestamp-gzip-dispatch-v1-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-gzip-dispatch-v1-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-gzip-dispatch-v1-oracle/check.py
```
