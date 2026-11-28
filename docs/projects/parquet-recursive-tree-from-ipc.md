# Strict Arrow V5 IPC to checked signed Tree Parquet

`Parquet.RecursiveSchema.Tree.Writer.FromIpc.convert` takes a modern
Arrow IPC stream and independent source and target limits. It uses
the shared recursive IPC admission check and the checked native
[Tree writer](parquet-recursive-tree-writer.md). The original recursive
declaration supplies the Parquet schema. Each completed RecordBatch
supplies one physical row group with its explicit row count, including
zero rows. A stream containing only a supported schema and EOS
produces a schema-only file. The output uses unindexed UNCOMPRESSED
PLAIN V1 with optional page CRCs.

## Admission and refusal

The source supplies signed INT32 and INT64 fields, Structs and LISTs.
The native writer requires a nonempty, named declaration with distinct
sibling names and nonempty Structs. A strict IPC stream can have an
empty declaration, including batches with rows at width zero, and
can admit unnamed or duplicate fields and empty Structs. Those cases
reach the existing typed writer refusal after exact EOS.

An opening failure returns the original typed schema or framing cause.
After opening, a batch or terminal failure returns the exact original
trace, including the schema, completed batches and first failure
ordinal and byte offset. Truncated EOS and bytes following EOS are
terminal failures. Source failures take precedence over target schema
checks and target budgets. A typed writer error implies that the
original source reached exact EOS. Refusals return no Parquet bytes.

## Certificate

`convert_readback` binds the original IPC schema frame and ordered
record frames through the EOS that ends the input to the native
construction and checked readback of the emitted bytes. `batch_group`
matches each original source RecordBatch to the native readback at
the same ordinal. The group retains the original checked leaf
witnesses, including exact repetition and definition levels, signed
words, positional paths and original page and slot coordinates.

## Verification

The pinned PyArrow V5 fixtures include mixed scalar and repeated
paths, signed extrema at both widths, nested siblings with independent
lengths, null and empty LISTs, null Structs and present all-null
Structs, schema-only IPC and a zero-row batch between populated
batches. The oracle compares the original IPC declaration, frame
offsets, counts and exact EOS, then checks the Lean-emitted Parquet
with checked native group reads, PyArrow and independent original
page inspection. Typed controls cover opening errors, late batch
errors, missing and extra terminal bytes, and source refusal ahead
of an exhausted or incompatible target.
[Fixture pins](../../scripts/parquet-recursive-tree-from-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-from-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-from-ipc-oracle/check.py
~~~
