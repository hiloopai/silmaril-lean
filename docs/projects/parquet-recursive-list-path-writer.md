# Canonical signed LIST-path Parquet writer

`ListPath.Writer.emit` accepts one named Arrow LIST field with a chain of
canonical LIST ancestors and one signed INT32 or INT64 leaf. Each node
has its own nullability. Input groups are ordered logical Arrow batch
observations with explicit row counts. The writer preserves null and
empty lists at each depth and null and present leaves. The input
declaration and signed width are retained in the original Parquet
schema. [Logical LIST-path core](parquet-recursive-list-path.md)

The writer emits one unindexed UNCOMPRESSED PLAIN Data Page V1 of
complete rows per group. An explicit zero-row group has a physical
zero-slot page. Zero groups produce a schema-only envelope. The
optional CRC covers the stored body. The shared Compact helpers write
the canonical LIST wrappers and the footer. Each column's original data
offset starts its frame, and both column sizes include the original
serialized header and body.

Schema depth and field budgets charge both physical entries for each
LIST, plus the root and leaf. Row, group, level and slot limits bound
the file and each page. Slot demand is checked before projection. The
exact body size is checked before level and word encoding, and the
header, chunk and file extents use the shared framing budgets.

## Construction and checked readback

`serialize_construction` proves successful construction from the
original compiled schema and the schema-directed projection. It binds
the ordered canonical repetition and definition levels and signed
words to the page bodies, Compact headers, contiguous offsets and
footer. `certify_readback` checks the completed bytes with the original
ListPath native reader. Successful certification recovers the exact
declaration, ordered logical groups, native group witnesses and direct
Events through EOS. `emit_wire` combines both guarantees for returned
files. [Native V1 reader](parquet-recursive-list-path-v1.md) · [Events](parquet-recursive-list-path-events.md)

The profile covers a single signed leaf under a positive bounded LIST
depth. Structs, multiple leaves, additional page versions and codecs,
dictionary encoding, indexed pages, pageless groups and binary Arrow IPC
input are outside this writer profile.

## Verification

Pinned PyArrow and independent Compact, Hybrid, CRC and signed-word
checks read 76 Lean files and 151 original pages at depths 1, 2, 3, 4,
6 and 16. Both signed widths cover every nullability combination at
depths 1–3 and required, optional and mixed shapes at deeper depths.
The existing one-LIST reader accepts the depth-one output, and depth-two
bytes match the existing TwoList writer. The tests cover signed extrema,
renamed fields, schema-only and explicit empty output, and optional CRC.
Full and empty Events preserve the complete groups through EOS.
Twenty-four typed controls check shape, bounds and readback mismatch.
[Producer and emitted byte pins](../../scripts/parquet-recursive-list-path-writer-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-writer-oracle/check.py
~~~
