# Two shared Parquet LIST ancestors ending in a Struct

`Parquet.RecursiveSchema.TwoListStruct` checks one canonical
LIST of LISTs whose innermost element is a required or optional
Struct with two signed INT32 or INT64 fields. Both LISTs and both
children have independent required or optional declarations. The checked footer
owns eight original SchemaElements. The physical depth budget admits
the seven entries on each leaf path, including the root and both
repeated wrappers. Each child retains its original path through the
Struct. An optional Struct adds one shared definition step.
[Single-leaf LIST paths](parquet-recursive-list-path-v1.md) · [One shared LIST ancestor](parquet-recursive-list-struct.md)

The reader binds exactly two positional chunks in each original row
group. This profile reads unindexed PLAIN UNCOMPRESSED V1. Each
column keeps the existing byte, page, row and slot bounds. The reader
checks the selected chunk's original frame versions before decoding
the payloads. It reuses the LIST-path reader's Compact framing, stored
CRC, exact prefixed Hybrid spans, signed words and both header-inclusive
totals. Its depth-two live-ancestry scan permits distinct legal V1
continuations on the two columns. The wrapper thresholds derive from
the checked nullable declarations.

The topology check compares the complete addressed traces in slot
order. Repetition distinguishes new rows, new inner LISTs and
continued innermost elements. Write `W` for the definition level after
both LIST wrappers, including any optional LIST steps. Null and empty
LISTs have distinct levels below `W`. A required Struct is reached at
`W`. An optional Struct is null at `W` and present from `W + 1`.
For an optional signed child, its own null has the Struct's presence
level, and a signed word has the next level. A required signed child
has a word at the Struct's presence level. The join clips definition
at that shared presence level and retains exact repetition. The first mismatch retains the
column paths, page ordinals, original absolute header offsets and
chunk slot ordinals of the available slots. The refusal proof
retains both independent chunk witnesses and the matched prefix.

Both child reconstructions use the existing checked LIST-path
inverse. For an optional element, a unary Struct on each path carries
its own child separately from shared presence. Merging two present
unary Structs keeps a present Struct even when both fields are null.
Row and LIST merges check equal lengths before pairing. Projecting
either signed child from the merged rows restores its
entire original ordered trace, including every repetition, definition
and signed word. The group theorem retains the original row count
and both original column witnesses. `readAll` keeps footer order.
Native Events expose both element nullability choices. The native
writer and strict IPC bridges use the required-element profile.
[Checked Arrow Events](parquet-recursive-two-list-struct-events.md) · [Native writer](parquet-recursive-two-list-struct-writer.md)

## Verification

Pinned PyArrow generates mixed INT32 and INT64 fixtures for all sixteen
nullability combinations. Independent checks inspect the Compact
footer and 188 original V1 pages from 17 accepted inputs, including an
authored reframe with separate repetition-one and repetition-two cuts
on both columns. Lean checks the original frame and section spans,
ancestry cursors, exact child slot sequences and reconstructed rows
across two groups. Four authored topology refusals keep each column
independently readable. Further controls exercise a closed inner
continuation, row and slot caps, the physical depth gate, and typed
admission of the required Struct, codec and V1 profile. The oracle checks eleven typed refusals.
[Producer and fixture pins](../../scripts/parquet-recursive-two-list-struct-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-oracle/check.py
~~~

The optional-element oracle checks all sixteen LIST and child
nullability choices in genuine PyArrow V1 files. Independent wire
inspection confirms 188 pages over 17 accepted inputs, including the
labeled reframe. The late presence control introduces two conflicts
and verifies the first with both original coordinates and the
completed group prefix under full and empty Events. The required-only
writer and IPC gates have separate controls.
[Optional-element fixture pins](../../scripts/parquet-recursive-two-list-struct-optional-element-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-optional-element-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-optional-element-oracle/check.py
~~~
