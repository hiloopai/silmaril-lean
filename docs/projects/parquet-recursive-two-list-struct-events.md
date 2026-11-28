# Arrow Events for two shared Parquet LIST ancestors

`TwoListStruct.Reader.Events` exposes the original native reader as a
recursive Arrow event stream. It takes one canonical LIST of LISTs of
required or optional Structs with two signed INT32 or INT64 fields, in unindexed
PLAIN V1/V2 with independently selected bounded LIST-path codecs.
The Arrow declaration preserves the original
outer LIST, inner LIST, Struct and child names and nullability. An optional Struct can be
null or present with independently null children.
[Native profile](parquet-recursive-two-list-struct.md)

`read` emits one batch for each complete original row group, in footer
order. A physical zero-row group emits a batch with count zero. A
schema-only file emits the declaration followed by EOS. The stream
ends with EOS when all groups succeed. A later refusal terminates after
the complete preceding batches and carries the group ordinal and
original typed cause, including the original addresses in topology or
child-page errors. Opening refusals precede the declaration.

`readProjected` takes `.field` for the full top-level field or `.empty`
for zero columns. Both selections run the same checks on both source
chunks and keep each explicit row count. The selected wire theorem
relates both declarations and the ordered observations to the original
reader, with a `Reader.GroupWire` witness for every completed group.
Accepted reframings with equal declarations and ordered observations
are equivalent under either selection.
[Strict Arrow IPC output](parquet-recursive-two-list-struct-to-ipc.md)

## Verification

The pinned PyArrow oracle checks 20 accepted inputs and 206 original
V1 pages in total. It covers all sixteen nullability choices, null
versus empty at both LIST depths, independently null signed children,
both signed width orders, renamed nested fields and schema-only EOS.
The labeled reframes exercise differing legal V1 cuts and a physical
zero-row group between populated groups. Seven typed refusals cover
opening errors, original topology and ancestry errors, and a late CRC
mismatch in the right original child. The oracle checks direct, full
and empty events against PyArrow's group observations and the
independently inspected original frames and error coordinates.
[Fixture pins](../../scripts/parquet-recursive-two-list-struct-events-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-events-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-events-oracle/check.py
~~~
