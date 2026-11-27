# Checked recursive Parquet schema and definition levels

`Parquet.RecursiveSchema.openFile` opens one immutable checked snapshot
and compiles its ordered SchemaElement vector. The root is a nonempty
unannotated group, with absent repetition or the legacy required marker.
Below it, required and optional unannotated groups and signed physical
INT32 and INT64 leaves are admitted. The profile refuses repeated nodes,
LIST and other converted or logical annotations, other physical types,
and type-length declarations. The existing snapshot validates schema
depth, sibling names, footer row totals and column order. The compiler
pairs its typed elements with the exact original raw schema items at
their ordinals, reads the original annotation fields, and consumes the
whole declared preorder under the depth bound.
[Parquet schema and Dremel definition levels](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding)

The compiled tree retains original names, sibling order and
nullability, and supplies the positional declaration for the
[recursive Arrow V5 writer](arrow-recursive-stream-writer.md). It also
stores a dense array of original physical leaves in preorder. Each
leaf carries its SchemaElement ordinal, full path excluding the root,
and the ordered optional declarations along that path, including an
optional leaf itself. Required declarations add no definition step.

At level `k`, the first `k` optional declarations are present. If `k`
reaches the maximum, the signed leaf value is present. Otherwise the
next optional declaration identifies the first absent site. This
distinguishes an absent group from a present group with a null child.
The level classifier takes the group-relative row coordinate supplied
by its caller. A level beyond the maximum returns that coordinate and
the original leaf path. The computed bit width is minimal, including
width zero for an all-required path.

`bindChunk` selects one original footer group and physical column. Its
result binds the exact chunk interval, path, physical type and row
count. Footer admission requires UNCOMPRESSED, an encoding list
containing PLAIN with only PLAIN and RLE entries, and no dictionary or
index page offsets. The compiler and binder end at the footer.
Individual page headers, level sections and signed payloads remain inputs
for the next reader. That reader must use independent column page cuts,
require shared ancestor agreement at each row, and assemble only
complete row groups before handing them to the Arrow stream writer.

The grammar witness binds each original node, child arity and path
extension to its raw and typed schema items. Separate laws pin each
selected leaf and each optional site to the original item, prove
the exact classification of definition levels, and identify the
original group list and immutable source. `ChunkBinding` carries
the metadata admission and source interval evidence directly.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-schema-oracle/Axioms.lean
python3 scripts/parquet-recursive-schema-oracle/check.py
```

Pinned PyArrow and Thrift check eight genuine files and one labeled
schema edit. Two different populated shapes reach beyond two levels,
and a schema-only file preserves the same declarations with zero groups.
Independent Python inspection reads real PLAIN V1 level and signed
payload bytes, aligns them by row, checks sibling agreement, and
reconstructs ordered nested rows for comparison with PyArrow. Lean
checks the compiled declarations and paths, original chunk intervals,
and classification of those independently read level words. The
fixtures cover missing optional ancestors, all-required paths, signed
endpoints, and typed annotation, repetition, codec, encoding, depth
and out-of-range refusals.
[Fixture pins](../../scripts/parquet-recursive-schema-oracle/fixtures.json)
