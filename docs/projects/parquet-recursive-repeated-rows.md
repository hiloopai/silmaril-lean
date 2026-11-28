# Checked recursive Parquet LIST row groups

`Parquet.RecursiveSchema.Repeated.Rows.readGroup` assembles an original
footer group using its checked recursive signed schema and original
unindexed UNCOMPRESSED PLAIN V1 and V2 chunks. The reader checks the exact
physical width and bounds the sum of the original level-entry counts
before decoding or allocating slot arrays. The row limit and each
chunk's existing limits apply as well. Every original column is
decoded before the group assembles its first logical row.
[Recursive schema](parquet-recursive-list-schema.md) ·
[Repeated chunk reader](parquet-recursive-repeated-chunk.md)

The reader attaches each slot's physical column path and ordinal,
page ordinal, header byte offset and absolute slot ordinal within
that chunk. It then partitions each column at repetition-zero starts
and checks the original row count. Page boundaries do not determine
row boundaries. A V1 row split across two pages is assembled as one row.

Assembly aligns the descendant columns of each logical list by
element ordinal. They must agree on null, empty, or live list state,
and live lists must agree on cardinality. Independent sibling lists
can have different lengths. Within each element, shared optional
Structs must agree on their own presence. A null element, a present
Struct with missing descendants, and a present Struct with all its
children null remain distinct. A disagreement carries both original
slot coordinates and the logical group, row and schema site.
Element-level errors also carry the enclosing list and element
ordinal. The assembler visits the common elements in order before
reporting a short column at the first unmatched slot. The short-column
error retains the available counterpart's original coordinates.
[Shared LIST-of-Struct topology](parquet-recursive-list-struct.md)

The typed assembler constructs `RowFits` evidence for the original
Arrow declaration. Its independent projection computes the expected
physical leaf sequences from the logical row and schema, including
repetition and definition words, classifications and signed values.
The reader checks that projection against the original column row
slices before returning the row. The partition proof restores every
original addressed slot in order, with exactly one row start in each
slice. The group theorem combines these records with `Chunk.Wire`
for every original column and the original row count. `readAll`
preserves footer order and group boundaries. This slice returns
logical row observations.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-repeated-rows-oracle/Axioms.lean
python3 scripts/parquet-recursive-repeated-rows-oracle/check.py
```

Pinned PyArrow supplies nested fixtures, independent list lengths,
and checksummed sibling chunks with different page cuts. The oracle
also compares the accepted authored mid-row split, a genuine
schema-only file and a labeled explicit zero-row group. Five labeled
edits keep every selected chunk valid while causing ancestor
presence, list state, cardinality, element presence or nested
Struct presence disagreement. Lean reports the original coordinates.
[Fixture pins](../../scripts/parquet-recursive-repeated-rows-oracle/fixtures.json) ·
[Predecessor chunk fixture pins](../../scripts/parquet-recursive-repeated-chunk-oracle/fixtures.json)
