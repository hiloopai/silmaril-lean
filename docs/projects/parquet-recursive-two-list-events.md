# Arrow events from checked two-LIST Parquet groups

The event adapter opens the unindexed PLAIN V1/V2 two-LIST profile
with identity or Snappy and exposes its exact recursive Arrow declaration once.
It uses the shared Parquet reader to emit one complete batch per
successfully reconstructed original group in footer order. Exhausting
those groups yields the Arrow event terminator `.eos`. A footer or
schema error is an open failure. A later read failure keeps its original
group ordinal and source cause, including the page address and incoming
cursor for a page error. Only complete earlier groups appear in the trace.
[Logical batch reader](parquet-recursive-two-list-rows.md)

## Projection and equivalence

The projection takes either `Selection.field` for the entire single
top-level field or `Selection.empty` for zero columns. Positions within
either LIST are outside this projection API. Projection runs after the
source read. It preserves the first reached terminal result, the count
of each complete batch, and the order of the corresponding row positions.
An empty projection can therefore return a nonempty row table with an
empty declaration.

The prefix theorem attaches a `Rows.GroupWire` witness to each erased
batch. If two checked sources have the same plan and ordered atom trace
in every corresponding group, the existing Rows reframe theorem gives
equal logical batches. The event theorem lifts that equality to the
shared observation of schema, ordered rows and termination. It applies
also to both supported projections.

## Existing IPC components

A bridge can reuse `Rows.readAll` to check the entire Parquet source and
`Rows.arrowSchema` to supply the original declarations, then call
`Arrow.RecursiveSchema.Stream.Writer.emit` with independent IPC bounds.
The existing batch planner recursively emits LIST offsets, validity and
signed child buffers for both LIST levels. The stream writer supplies
exact EOS and checked stream readback. A bridge can combine that readback
with the event prefix law to relate native IPC to the direct events.
[Recursive Arrow batch writer](arrow-recursive-batch-writer.md) · [Recursive Arrow stream writer](arrow-recursive-stream-writer.md)

## Fixtures and regressions

Pinned PyArrow generates INT32 and INT64 two-LIST files with three unequal
row groups and a schema-only file. Independent
Compact, Hybrid and signed-word inspection checks the original frames
and each labeled reframe. The reframes start pages at repetitions one and
two and preserve the same observations under both projections.

The failure fixtures include an inner continuation in the second group
and a page CRC failure in the third. In the file with both errors the
incomplete second group and later group emit no batch. Empty projection
keeps the exact prior group counts and the same addressed failure.
[Producer and fixture pins](../../scripts/parquet-recursive-two-list-events-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-events-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-events-oracle/check.py
~~~
