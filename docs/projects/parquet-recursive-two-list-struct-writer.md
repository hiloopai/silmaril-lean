# Native Parquet writer for two LISTs of Structs

`TwoListStruct.Writer.emit` takes an Arrow recursive declaration and
an ordered list of logical group observations with explicit row counts.
The declaration has one canonical LIST of LISTs whose elements are
required or optional Structs with two signed INT32 or INT64 children. Both LISTs
and both signed children have independent nullability. The original
field names are written in the Parquet schema and physical paths.
[Native reader profile](parquet-recursive-two-list-struct.md)

Each group writes two consecutive unindexed UNCOMPRESSED PLAIN V1
pages, one per signed child in declaration order. Both pages represent
complete rows. The writer projects the children using the shared LIST
topology and reuses the ListPath writer for exact repetition and
definition levels and signed words. Each optional child path wraps its
leaf in a unary Struct. A null Struct contributes the shared absence
marker to both columns. A present Struct with two null children
contributes the shared presence level to both columns. The existing Compact assembler
writes both original page offsets, slot counts and header-inclusive
sizes. CRC is optional. An explicit zero-row group writes two physical
zero-slot pages. Zero groups produce a schema-only PAR1 file.

The writer checks schema depth, schema extent, group and row counts,
and slot demand before projection. Each null or empty LIST and each
reached Struct contributes one slot per column. The proof identifies
this preflight count with both projected traces and charges both
columns to the total slot limit. The shared page builder enforces per-column level, page,
header, body and chunk bounds. Compact footer and file bounds apply
to the final carrier. Incompatible declarations, malformed rows,
and count or budget violations return typed errors.

`serialize_construction` relates both emitted frames to the two
canonical child projections and the final Compact envelope.
`certify_readback` separately checks the original bytes with the native
reader. Successful readback binds the exact intended declaration,
the explicit count and rows of every ordered group, and both
`Reader.GroupWire` column, byte-range and addressed slot witnesses.
The strict IPC bridges admit required Struct declarations.
[Strict Arrow IPC input](parquet-recursive-two-list-struct-from-ipc.md)

## Verification

Pinned PyArrow and independent Compact, Hybrid, signed-word and CRC
checks read 34 Lean-emitted PAR1 files and 134 original V1 pages.
The oracle covers all sixteen nullability choices in both width
orders, signed extrema, renamed fields, both CRC settings, a
physical zero-row group between populated groups, and a schema-only
file. Twenty-one typed controls cover malformed declarations and
rows, output bounds and exact readback mismatch.
[Fixture pins](../../scripts/parquet-recursive-two-list-struct-writer-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-writer-oracle/check.py
~~~

The optional-element oracle checks another 34 files and 134 pages.
It covers both signed width orders, all sixteen LIST and child
nullability combinations, renamed fields, signed extrema, both CRC
settings, schema-only and physical zero-row groups. Twelve typed
controls include required signed children, malformed Struct cells,
per-column and total budgets, and readback with null Struct and
present all-null Struct observations exchanged.
[Optional-element writer fixture pins](../../scripts/parquet-recursive-two-list-struct-optional-element-writer-oracle/fixtures.json)

~~~sh
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-optional-element-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-optional-element-writer-oracle/check.py
~~~
