# Strict Arrow V5 IPC import to TwoListStruct Parquet

`TwoListStruct.Writer.FromIpc.convert` reads strict recursive Arrow
V5 IPC and invokes the checked native writer for one canonical LIST
of LISTs of required or optional Structs with two signed INT32 or INT64 children.
Original field names and nullability remain part of the declaration.
Each complete source batch becomes one original Parquet row group
with two unindexed UNCOMPRESSED PLAIN V1 pages. A zero-row batch
writes two zero-slot pages. A schema-only stream writes zero groups.
CRC is optional.
[Native writer](parquet-recursive-two-list-struct-writer.md)

The shared IPC admission check, also used by ListPath, retains the full
typed opening error or terminal trace with the original ordinal, byte
offset, cause and completed batch prefix. Exact EOS precedes declaration
validation and target admission. An unsupported shape or absent name
returns the complete source trace after EOS, before target budgets
are applied. An admitted declaration may still hit a typed native
writer error. Every refusal returns an error without Parquet bytes.

`convert_readback` binds the original IPC schema, exact ordered
batches and terminal EOS to the construction and checked native
readback of the emitted Parquet file. The witness retains the explicit
counts and rows and each group's original child paths, frame spans
and addressed signed slots. When the forward bridge succeeds,
`round_trip` certifies exact strict IPC readback of the selected
declaration and the corresponding observation of every original batch.
The empty selection keeps each count with zero columns.
`round_trip_parquet` also relates a full-field export and reimport
to the original Parquet declaration and group observations, with
the original addressed group witnesses on both native carriers.
[Forward bridge](parquet-recursive-two-list-struct-to-ipc.md)

## Verification

Pinned PyArrow and separate IPC and Parquet wire checks cover 34 genuine
Arrow inputs, 134 original Lean-emitted V1 pages and 68 returned IPC
streams through exact EOS. The cases include both width orders, all
sixteen nullability choices, signed limits, renamed fields, schema-only,
a physical zero-row group and both CRC settings. Nineteen typed controls
cover malformed envelopes and records, exact EOS, absent names,
unsupported declarations and independent source and target budgets.
Late failures and declaration refusals retain the original trace under
exhausted target limits.
[Fixture pins](../../scripts/parquet-recursive-two-list-struct-from-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-from-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-from-ipc-oracle/check.py
~~~

The optional-profile oracle additionally checks 36 genuine Arrow
inputs, 138 emitted Parquet pages, 72 selected IPC returns and eleven
typed controls. It includes a PyArrow stream with nonzero physical
words in both required child slots under a null Struct. Checked
projection discards those hidden words while retaining the signed
values under a present Struct. The previous optional-Struct refusal
fixture is admitted using the same original IPC bytes.
[Optional-profile verification commands](parquet-recursive-two-list-struct-to-ipc.md#optional-struct-verification)
