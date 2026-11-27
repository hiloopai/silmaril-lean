# Checked recursive Arrow IPC V5 schema

`Arrow.RecursiveSchema.readFrame` reads the first modern little-endian V5
Schema frame and returns the ordered field tree and the byte offset after the
padded metadata. `readMessage` takes the original padded metadata directly.
The profile ends at the Schema frame. Record batches and stream EOS are
outside its scope.
[Arrow Message IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Message.fbs) ·
[Arrow IPC framing](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#encapsulated-message-format)

The AST keeps each optional UTF-8 name, nullability flag, type, and child
position. The admitted union variants are signed Int with bit width 32 or
64 (tag 2), List with exactly one child (tag 12), and Struct with an ordered
vector of any length (tag 13). An integer has no children. Empty schemas,
empty Structs, and repeated names have positional interpretations. The
profile requires a bodyless Schema and refuses dictionaries, other type
variants, custom metadata entries, schema features, unsupported versions,
and big-endian metadata.
[Arrow Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

The checked FlatBuffers inspectors bound each vector's extent before walking
its offset words. Errors identify the original metadata-relative Field
table or offset word for local failures. Root fields have depth one. A
child is decoded with one less unit of depth, and each visited Field consumes
one unit of the shared `ipc.fields` budget. Siblings receive the unused
budget after the preceding subtree. Every occurrence counts, including
multiple references to the same table.

`readMessage_wire` binds the result to the original root vector and every
original offset word and Field table, in order and at the admitted arity.
The witness accounts for the total field occurrences and indexes each child
vector at strictly smaller depth. `readFrame_wire` additionally identifies
the exact original framed metadata slice and the following byte offset.
The existing flat and fixed-shape schema readers retain their entry points.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-schema-oracle/Axioms.lean
python3 scripts/arrow-recursive-schema-oracle/check.py
```

The oracle pins CPython 3.13.5, PyArrow 26.0.1, seven genuine IPC streams
and six labeled edits. PyArrow and the independent FlatBuffers inspector
agree on the nested stream's 11 fields across four levels, including nested
Lists and Structs, signed widths, Unicode names, repeated names, and
nullability. The comparator checks the Lean tree, its local vector and table
positions, and the cursor before the genuine following batch. It also covers
an empty schema at both zero limits and 16 typed refusals, including one-short
depth and total-field budgets, malformed nested vectors and offsets, and
invalid List arities.
[Fixture pins](../../scripts/arrow-recursive-schema-oracle/fixtures.json)
