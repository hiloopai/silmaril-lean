# Recursive signed Parquet file writer

`Parquet.RecursiveSchema.Repeated.Writer.emit` accepts an Arrow recursive
schema and ordered logical row-group observations. It emits a plaintext
PAR1 file with UNCOMPRESSED PLAIN Data Page V1 and signed INT32/INT64
leaves. The profile supports required and optional Structs and canonical
three-level LIST with at most one repeated ancestor per physical leaf.

## Schema and groups

The schema inverse writes the actual Compact entries in preorder. Each
List has its annotated outer group, repeated `list` wrapper and original
element declaration. The original compiler opens a native schema-only
file and checks exact Arrow declaration equality, ordered entries,
footer extent and zero groups. The file writer uses these compiled leaves
and the same schema entries in its final footer. Named fields retain
their original UTF-8 text, including empty names. Missing names,
duplicate sibling names, an empty root or Struct, invalid arities,
nested List ancestry and exhausted schema budgets are typed refusals.

Each input group supplies an explicit row count and logical rows. The
writer checks the count and budgets projected slot demand before
expanding List elements. The original row projection validates the
typed cells, including required fields, and yields the physical leaf
atoms in order. A caller can supply an explicit page partition for each
physical leaf, given as slot counts in preorder. Every partition exhausts
the original projected atoms. Leaf cuts are independent and can split a
live List. The default is one page per leaf. A zero-row group has one
empty page per leaf, with an explicit cut of `[0]` when specified.

## File construction and verification

The file cursor advances by each emitter's actual header-inclusive
chunk length. Its footer uses the compiled physical paths, certified
chunk slot counts, cumulative data-page offsets and actual encoded
sizes. Row counts come from logical group lengths and every chunk
independently certifies that count. The file row total sums the ordered
groups. Compact writers check signed integer widths. The PAR1
trailer records the exact bounded Compact footer size.

Admission bounds the groups, rows, slots, pages and bytes across the
file and the applicable row-group, chunk, page and Compact budgets.
A leaf receives the remaining file byte and page budgets. The optional
CRC policy applies to all pages.

`Schema.emit_wire` certifies the schema inverse. `writeColumn_wire`
ties an exact partition to the original chunk writer, packed bytes
and metadata placement. `serialize_construction` identifies the
checked schema, packed payload and original native envelope.
`emit_wire` certifies that the existing `Repeated.openFile` and
`Rows.readAll` recover the exact schema, footer, ordered logical rows
and group counts from the same bytes. Each returned group has its
original `Rows.GroupWire`. These are success guarantees for the
admitted profile. The Arrow IPC file bridge is a later layer.

## Interoperability checks

Pinned PyArrow and independent Compact, page and level inspection check
three complete Lean outputs containing 15 native chunks and 17 pages.
They cover signed endpoints, optional CRC, the distinctions among
null and empty Lists, null elements and present Structs, independently
cut sibling chunks with a mid-row continuation, groups of 3, 0 and 2
rows, and a schema-only file retaining an empty name. All positive
files are written entirely by Lean. Twenty-five typed controls exercise
unsupported schemas, invalid rows and partitions, and cumulative
bounds, including a byte refusal in the second group.

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-file-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-file-writer-oracle/check.py
```
