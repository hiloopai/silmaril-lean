# Ordered Parquet TIMESTAMP projection to typed Arrow Events

`Timestamp.Leaf.Projection.readAll` opens one checked Parquet
snapshot, applies the input and width limits, and binds the requested
modern flat INT64 TIMESTAMP leaves before reading any row group. Each
position carries a proof that its binding is modern and belongs to
that snapshot. Column opens and group reads use the caller's order.
The serialized leaf ordinal is 1-based, with index zero reserved for
the root. Projection positions and row-group indices are zero-based.

Repetition and width zero follow the positional policy in
FlatProjection. Repetition produces the same field and values at each
requested position and contributes to the input width cap. An empty
selection emits a zero-width aligned batch with the original row
count for each group that passes the common row check. It requires
no leaf binding or payload read. An input with no groups has no
batches. Each nonempty projection field retains its own name,
nullability, millisecond, microsecond or nanosecond unit, and UTC or
local epoch interpretation. The profile uses the existing AllCodecs
dictionary and scalar routes for the selected leaves.

One failed column prevents a batch for that group. The error records
the original group and leaf ordinal, the position in the projection,
and the original AllCodecs cause. Earlier completed groups remain in
the trace. A group count or row bound error is shared by all
projections of the same checked source, including width zero.

## Projection laws

A successful group's columns agree with the corresponding standalone
AllCodecs leaf reads. The batch row count is exactly the original
footer count. Reading a projected checked selection agrees with
logical Arrow Events projection of every successfully read group,
including reordered or repeated fields and zero-width batches.
When the wider trace reaches EOS, `Trace.scan` with a true predicate
equals the trace of the checked selection, with the same batch
boundaries. The resulting event streams are observationally equivalent.

Logical projection carries the wider trace's terminal error.
Physical projection skips the omitted column reads. At the wider
trace's first failed group, the narrower source can continue exactly
when the shared group checks and every selected read at that group
succeed. If a selected read still fails there, the first failure is
reported in the narrower order. Physical projection can reach EOS
while the wider trace fails exactly when all shared checks and all
selected reads succeed across the footer, and at least one omitted
position fails. Shared Snapshot admission applies before these
projection laws.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Projection/Thms.lean) ·
[Existing FlatProjection policy](../../Silmaril/Formats/Parquet/FlatProjection/Defs.lean) ·
[AllCodecs profiles and limits](parquet-timestamp-all-dictionary-v1.md)

## Independent evidence

Genuine pinned PyArrow V1 and V2 files each contain three groups and
three TIMESTAMP columns plus an INT32 decoy. They cover nullable UTC
nanoseconds, required local microseconds, and nullable UTC
milliseconds, with signed extrema and repeated counts. Thrift
checks the annotations, codec and page tags, dictionary/data offsets,
and stored CRCs. The comparator checks actual Lean Events against
independent PyArrow counts, including a reordered and repeated
selection, smaller direct selections, empty projections, and a
schema-only file.

The separately labeled CRC mutation damages the Zstandard
dictionary of the local column in the second group. PyArrow rejects
that selected chunk and reads the unaffected ones. Lean reports
the original offsets and retains the first complete group. Reordering
the selected failure changes its projection position. Logical
projection retains the error and prefix, while omitting the failed
column at read time yields every group through EOS. The comparator
also checks invalid ordinals and field and group-row caps.

[Comparator](../../scripts/parquet-timestamp-events-projection-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-events-projection-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-events-projection-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-events-projection
/tmp/parquet-timestamp-events-projection/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-events-projection/bin/python -I scripts/parquet-timestamp-events-projection-oracle/check.py
```
