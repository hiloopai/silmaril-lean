# Native recursive Arrow IPC V5 stream writer

`Arrow.RecursiveSchema.Stream.Writer.emit` takes one explicit
[recursive schema](arrow-recursive-schema.md) and a list of ordered
[logical batch observations](arrow-recursive-rows.md). It emits one
bodyless V5 Schema, one native uncompressed RecordBatch per observation,
and the eight-byte modern EOS at the exact end. The profile covers
little-endian signed INT32 and INT64, ordered Struct children, and List
fields with one child. The schema keeps optional, empty and repeated names
in their original positions. An empty batch has its own frame. A
positive-count, width-zero batch carries its count in its metadata.
[Arrow IPC stream format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-streaming-format)

`serialize` checks the batch count before either constituent writer builds
bytes. The schema writer then checks the declaration. The
[RecordBatch writer](arrow-recursive-batch-writer.md) plans and serializes
batches in input order. A refusal carries the original schema or batch
writer cause. A batch refusal also gives its zero-based input ordinal.
The result on failure contains only the typed error. `emit_batch_error`
identifies the first failed input and witnesses complete serialized
frames for its earlier observations.

`emit` then runs the existing strict recursive stream reader once over the
assembled carrier. Its comparison uses the same schema and logical-row
equality checks as the constituent writers. The component serializers
retain their existing admission and metadata checks.

The construction laws give the exact bodyless Schema, ordered batch
frames, native EOS, and concatenated byte lengths. The separate
`emit_readback` law gives the original schema and ordered observations,
the independent reader cursor chain, and a modern EOS consuming the
remaining eight bytes. These laws apply to successful writes. The
logical round trip permits canonical hidden Struct slots and empty
physical windows under null Lists, as specified by the batch writer.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-stream-writer-oracle/Axioms.lean
python3 scripts/arrow-recursive-stream-writer-oracle/check.py
```

Pinned PyArrow independently reads five actual Lean streams with nine
batches. Raw inspection pins the schema end, each original output frame
start, metadata and body extents, and the final EOS. The comparator checks
four levels of nesting, signed endpoints, repeated names at root and
child positions, explicit empty and schema-only cases, and positive row
counts at width zero. Seven typed refusals include batch-count precedence,
two different late ordinals in the same source sequence, and a late
required-null refusal.
[Fixture pins](../../scripts/arrow-recursive-stream-writer-oracle/fixtures.json)
