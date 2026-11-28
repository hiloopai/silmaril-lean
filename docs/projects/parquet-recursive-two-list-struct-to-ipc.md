# Strict Arrow IPC for two shared Parquet LIST ancestors

`TwoListStruct.Reader.ToIpc.convert` takes the native unindexed
UNCOMPRESSED PLAIN V1 profile for a canonical LIST of LISTs of required or optional
Structs with two signed INT32 or INT64 children. It produces a strict
Arrow V5 IPC stream using the checked Events adapter and the existing
recursive stream writer.
[Native profile](parquet-recursive-two-list-struct.md) · [Events](parquet-recursive-two-list-struct-events.md)

Full-field selection retains the original nested names and nullability.
Empty selection writes the empty declaration and a zero-column batch
with the original count for each group. A physical zero-row group
contributes a batch in either selection. A schema-only source contributes
the declaration and EOS.

The converter reaches native EOS before writer admission. An opening
refusal carries the original typed cause. A group refusal carries the
original group error and the complete selected prefix, including the
coordinates retained by the native topology and page checkers. Both
refusals precede target budget checks and return no IPC bytes.

Checked output readback ties the selected declaration and ordered
observations to the original input and the `Reader.GroupWire` witness
for every source group. The proof uses the strict recursive reader's
cursor chain, including the exact eight-byte terminal EOS and its batch
ordinal.

## Verification

The Events oracle supplies 18 genuine PyArrow sources and two
labeled reframes. A separate parser checks the IPC schema, node and buffer
vectors, validity, List offsets, signed words and exact EOS for all 40
Lean-emitted streams. Coverage includes both signed width orders, all
sixteen nullability choices, renamed nested fields, schema-only EOS, a
labeled physical zero-row group and an independent page reframe.
The native and reframed inputs produce identical streams under both
selections. Seven typed source refusals cover opening, topology,
ancestry and CRC with both normal and exhausted writer budgets where
applicable. Seven writer controls cover the batch, row, depth, slot
and body limits. Strict readback also checks appended and truncated
terminal markers.
[IPC fixture pins](../../scripts/parquet-recursive-two-list-struct-to-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-to-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-to-ipc-oracle/check.py
~~~

## Optional Struct verification

The strict IPC writer uses the existing Arrow Struct validity and
child visibility rules. A null Struct has an invalid parent slot.
Its hidden signed slots use canonical valid zero words, including
when the child is required. A present Struct with two null children
keeps a valid parent and two visible null child slots. The source
and writer certificates preserve the resulting logical distinction.

The oracle checks 20 optional Parquet sources across 206 original
V1 pages. It verifies 40 Lean IPC streams through exact EOS and 20
full-field native returns. Cases cover independent page cuts, renamed
fields, both signed widths, CRC and no CRC, schema-only files, and
physical zero-row groups. An authored late Struct-presence mismatch
retains both original coordinates and the complete selected prefix
under exhausted IPC limits. The same oracle checks the IPC import
direction and preserves the required-profile pins.
[Optional IPC bridge fixture pins](../../scripts/parquet-recursive-two-list-struct-optional-element-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-optional-element-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-optional-element-ipc-oracle/check.py
~~~
