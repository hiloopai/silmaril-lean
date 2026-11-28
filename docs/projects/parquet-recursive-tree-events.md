# Native Arrow Events for recursive Parquet trees

`Parquet.RecursiveSchema.Tree.Rows.Events.read` uses the checked
[Tree row-group reader](parquet-recursive-tree-rows.md) and the common
Parquet adapter for Arrow Events. It opens the original footer and
emits the recursive Arrow declaration from the checked Tree plan.
Nested names, field order, nullability and signed widths are carried
by that declaration. The exact native reprojection proves the rows
fit it, including null and empty LISTs, null Structs and present
Structs with null children.

The stream contains one batch per complete original row group in
footer order, including a physical zero-row group. A schema-only
file emits its declaration and EOS. A footer or compiler refusal
is an open error. Once a declaration is emitted, each group uses
the existing Tree binding and read order. The first native failure
terminates the stream with its original group ordinal and typed
cause. For a failed leaf or shared occurrence, the cause retains
the original coordinates. All earlier complete batches remain in
the trace.

## Projection

`readProjected` uses the same dependent `Scan.Projection` as Arrow
RecursiveSchema Events. The caller can use `Projection.id` for all
fields or `Projection.ofArray` for a checked ordered array of source
positions. Positions have type `Fin source.width`, so reordering,
repetition and the empty array are valid views. Positions outside the
declaration cannot be represented by this API.

Every original leaf is bound and checked before its complete group
is projected. Selecting zero columns preserves the number of rows
and batches. The projection laws identify the selected declaration
and every batch's positional cells with the corresponding view of
the full trace. Both views share its first terminal result.

## Evidence and verification

Each complete batch is tied to its original `Tree.Rows.GroupResult`.
The native certificate gives exact signed reprojection and original
wire witnesses for each physical column. The ordered prefix theorem
ties projected observations to the same checked results. The
terminal failure theorem identifies the exact original group read
after that prefix. For a shared mismatch, the native refusal
theorem then recovers the checked original boundaries.

Pinned PyArrow inputs cover branching V1 and V2 sources, unequal
independent LIST lengths, multiple top-level fields, renamed nested
fields, mixed signed widths and present all-null Structs. The
oracle compares every observed batch and explicit count against
the PyArrow row groups under direct, full, reversed, first-field
and empty views. It includes a schema-only source and a labeled
physical zero-row group. The late shared-presence case retains a
complete preceding batch. Adding a stored CRC failure in the last
physical leaf returns that original page error before the pending
shared disagreement, including under empty selection.
[Producer and fixture pins](../../scripts/parquet-recursive-tree-events-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-events-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-events-oracle/check.py
~~~
