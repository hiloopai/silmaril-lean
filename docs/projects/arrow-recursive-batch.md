# Checked recursive Arrow IPC V5 RecordBatch layout

`Arrow.RecursiveSchema.Batch.readFirst` binds the original framed
[recursive schema](arrow-recursive-schema.md) to its first RecordBatch.
`readFrame` can check a subsequent RecordBatch against the same schema at
the returned cursor. The planner consumes one FieldNode per field and the
field's own buffer descriptors before visiting its children in schema order.
It requires exact consumption of both descriptor vectors.
[Arrow 26.0.1 Message IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Message.fbs) ·
[Arrow 26.0.1 IPC format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

Each root uses the batch row count. A Struct has a validity region and each
child uses the Struct length. A List has validity and signed little-endian
INT32 offsets. The first offset must be zero and all `length + 1` logical
offsets must be nonnegative and nondecreasing, including those under null
parents. The original final word determines the required length of its
single child. The declared offsets region may contain additional bytes, as
in a genuine sliced empty PyArrow batch. An INT32 or INT64 leaf has validity
and an exact four- or eight-byte value region per slot.

The planner checks descriptor alignment, ordering, and containment in the
declared body. Padding between and after regions is allowed. It bounds each
declared null count by its node length and checks bitmap availability and
extent. Actual bitmap bits, requiredness under parent nulls, and primitive
values are outside the layout observation. The per-batch slot budget counts
the sum of physical lengths across all FieldNodes. The existing IPC byte,
field, and row limits and the schema depth limit also apply. Errors identify
the original zero-based node, buffer, or List offset word where applicable.

The profile admits modern little-endian V5, uncompressed bodies, and the
original signed INT32, signed INT64, Struct and List schema types. Compression,
nonempty variadic counts, dictionaries, and unsupported metadata are typed
refusals. Batch iteration and stream EOS are caller responsibilities.

`First.wire` identifies the exact original schema metadata and batch
envelope. `Frame.wire` binds the layout to every consumed original indexed
FieldNode and Buffer, the exact body, and the slot bound.
`Frame.region_exact` gives the absolute carrier range of a checked buffer.
`OffsetPrefix.last_word` and `OffsetPrefix.window` identify the original
terminal and adjacent signed offset words. The List wire constructor ties
the terminal word to the checked child's length.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Batch.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-batch-oracle/Axioms.lean
python3 scripts/arrow-recursive-batch-oracle/check.py
```

The pinned PyArrow producer reuses the exact four-level schema metadata from
the schema oracle. Its new populated batch includes signed endpoints,
nested Lists and Structs, and a null Struct slot. The independent comparator
checks all original node words, buffer descriptors, physical regions, and
logical List offsets. It also checks a following sliced empty batch and a
genuine two-row batch at width zero. Four genuine IPC pins and 19 labeled
edits cover 24 typed refusals and a bitmap-content control.
[Fixture pins](../../scripts/arrow-recursive-batch-oracle/fixtures.json)
