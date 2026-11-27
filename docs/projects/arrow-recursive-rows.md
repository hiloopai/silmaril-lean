# Logical rows of one checked recursive Arrow IPC batch

`Arrow.RecursiveSchema.Batch.Rows.decode` projects one
[checked RecordBatch](arrow-recursive-batch.md). The native `readFirst`
entry point binds the original schema and first batch in the same carrier.
Both reuse the [physical semantics](arrow-recursive-semantics.md) for the
uncompressed little-endian V5 signed INT32, signed INT64, Struct and List
profile. Layout and physical failures retain their original typed causes.

The result uses ordered lists of optional cells, as in the flat Arrow
observation. Its recursive values carry signed INT32 and INT64 words,
ordered Struct fields, and ordered List elements. Names, nullability and
child declarations come from the original schema. A null parent yields a
null cell immediately. A present Struct with all-null children has its own
Struct value. A present empty List has a List value with zero elements.
Child slots in an absent Struct or a null List's physical window produce
no logical values. The RecordBatch row count remains explicit, and a
positive count at width zero yields that many empty rows.

Signed word vectors are converted to arrays once. A Struct visits each
visible child at the same index. A List enumerates the original half-open
window in child order using array lookups for bits, signed words and
offsets. Depth comes from the checked schema limit. The checked windows
are disjoint, and each visible child slot is visited at most once during
projection. Native admission uses the existing body, slots and row limits.
Stream iteration and EOS are caller responsibilities.

`decode_wire` and `readFirst_wire` compose the independent logical slot
relation with the original physical witness. `ProjectionWire.row_at`
binds each row to its original slot and positional columns. The witness
gives both the exact original row count and conformance of every row to the
ordered schema, including nested nonnullable declarations. A null cell
has no descendant premises. `validity_at` and `signedWord_at` identify
the original bitmap bit and exact byte slice; List cells use the original
offsets and their ordered child interval. `project_total` proves that every
checked physical observation projects successfully.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-rows-oracle/Axioms.lean
python3 scripts/arrow-recursive-rows-oracle/check.py
```

Pinned PyArrow checks six native batches across four genuine streams.
The oracle compares `to_pylist` values by position, including duplicate
root names, signed endpoints, hidden required nulls, a present all-null
Struct, a null List with a nonempty physical window, and an empty List.
It independently checks the raw row-count word of the two-row zero-width
batch. Eight labeled edits include a bitmap padding control and a late
null-count error in a second populated batch. The unchanged earlier batch
produces the original rows and the later batch retains its typed source
failure.
[Fixture pins](../../scripts/arrow-recursive-rows-oracle/fixtures.json)
