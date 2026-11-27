# Native recursive Arrow IPC V5 schema writer

`Arrow.RecursiveSchema.Writer.emit` serializes one bodyless little-endian
[recursive Schema](arrow-recursive-schema.md) followed by the explicit
modern eight-byte EOS. The admitted types are signed INT32, signed INT64,
Struct, and List. Struct children remain ordered, a List has exactly one
child, and an integer has no children.
[Arrow Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[Arrow IPC stream format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-streaming-format)

Each Field retains its original optional UTF-8 name and nullable flag.
An omitted name slot and a present empty string have distinct encodings.
Repeated names have separate positions. The writer uses the existing
V5 Message prefix, Schema payload, forward vector offsets, and stream
envelopes. The recursive fragments retain the shared Field table position
at byte 12. Their Field vtable follows the table object, with a signed
displacement of −20. Child references target their original positional
fragments. The writer emits one schema and ends the stream without batches.

Before constructing bytes, `plan` checks each field's arity and depth,
one total occurrence budget, and the cumulative padded metadata size.
A typed error gives the zero-based preorder ordinal for an arity, depth,
or occurrence failure. The configured metadata cap and the signed
32-bit framing range bound the output before strings, vectors, or
offset words are assembled.

The construction laws give exact header, prefix and metadata extents.
`Wire.offsets_target` and `Wire.offsets_forward` give the positional
target formula and forward bounds for the shared vectors. The measured
extent in `serialize_extent` is the extent actually used by the native
envelope. `emit` then certifies the offered schema, an empty batch sequence,
and exact EOS with the existing strict reader. `emit_wire` proves the
result of this readback check as well as the byte construction.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-schema-writer-oracle/Axioms.lean
python3 scripts/arrow-recursive-schema-writer-oracle/check.py
```

Pinned PyArrow and an independent raw FlatBuffers observer read all five
actual Lean streams. Genuine inputs cover the four-level schema, an
explicit empty name, repeated names at root and child positions, and zero
width. The pinned PyArrow field API requires a string. The absent-name
control is a labeled edit of one original name reference. Raw inspection
observes the missing slot in the emitted bytes, and PyArrow presents it
as an empty string. The comparator pins the five emitted carriers and checks
eight typed refusals, including exact depth, field and size boundaries.
[Fixture pins](../../scripts/arrow-recursive-schema-writer-oracle/fixtures.json)
