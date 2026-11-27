# Native recursive Arrow IPC V5 RecordBatch writer

`Arrow.RecursiveSchema.Batch.Writer.emit` writes one modern continuation
envelope, one V5 RecordBatch message, and its aligned body. It takes an
explicit [recursive schema](arrow-recursive-schema.md) and a
[logical observation](arrow-recursive-rows.md) with a row count. Signed
INT32, signed INT64, ordered Struct children, and single-child List fields
use the existing little-endian, uncompressed profile. Empty batches retain
their descriptor vectors. A width-zero batch has empty vectors and body
and carries its explicit row count in native metadata.
[Arrow IPC format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#recordbatch-message)

The plan checks row count, row and Struct width, value kind, visible
required slots, field arity, and depth. Errors for field and slot
admission use zero-based preorder node and physical slot ordinals.
Struct children inherit the parent slot count. List children concatenate
present windows in order. Before expanding direct Struct columns or
concatenating List slots, the planner checks the required workspace against
the physical slot budget. The signed INT32 terminal List offset bounds
every offset in its vector. The planner accounts for metadata and padded
body bytes incrementally and completes all checks before constructing wire
buffers. Signed message lengths and the existing IPC and recursive
limits apply.

The writer emits the minimal bitmap extent for each node, including an
all-valid node, with zero trailing padding bits. Null integers carry a
zero physical word. A null Struct gives every hidden child a valid
physical slot, with zero integer words, recursively hidden Struct
children, and empty List windows. A null List uses an empty physical
window. Parent validity distinguishes absent Structs from present
Structs with null fields, and absent Lists from present empty Lists.
These choices give canonical physical bytes for the logical rows.
Re-emitting an existing stream can change its hidden physical values
and null List windows.

The construction laws identify each bitmap bit, little-endian word and
List offset. `encode_wire` gives the planned node order, buffer count,
padded body extent, and exact packed regions. `serialize_frame` relates
these components to the existing native framing and metadata builders.
`emit_wire` certifies successful emission using the unchanged
`Batch.readFrame` and `Rows.decode`. It recovers the exact logical input
under the supplied schema, with the independent recursive wire witness,
and consumes the entire emitted batch frame. The frame API is independent
of stream assembly. The interoperability driver adds the existing
bodyless Schema and explicit modern EOS around the emitted frames.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms +Silmaril.Formats.Arrow.RecursiveSchema.Writer.Thms +Silmaril.Formats.Arrow.StreamWriter.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-batch-writer-oracle/Axioms.lean
python3 scripts/arrow-recursive-batch-writer-oracle/check.py
```

Pinned PyArrow reads the seven actual Lean batches in five streams.
The independent inspector reconstructs the canonical node and buffer
vectors and all body bytes from the producer's positional logical values.
The fixtures cover a four-level tree, independently nullable children,
hidden slots with a nonempty original null List window, signed endpoints,
values outside INT32, repeated root and child names, a second bitmap
byte, explicit empty batches, positive counts at width zero, and a
schema-only control. Fifteen typed refusals cover shape, requiredness,
field and depth bounds, and resource caps. The signed List offset boundary
is checked directly without allocating a large array.
[Fixture pins](../../scripts/arrow-recursive-batch-writer-oracle/fixtures.json)
