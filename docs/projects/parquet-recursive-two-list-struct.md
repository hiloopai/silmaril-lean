# Two shared Parquet LIST ancestors ending in a Struct

`Parquet.RecursiveSchema.TwoListStruct` checks one canonical
LIST of LISTs whose innermost element is a required Struct with two
signed INT32 or INT64 fields. Both LISTs and both children have
independent required or optional declarations. The checked footer
owns eight original SchemaElements. The physical depth budget admits
the seven entries on each leaf path, including the root and both
repeated wrappers. The required Struct adds no level increment.
Each child retains its original path through the Struct.
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
continued innermost elements. Definition levels below the shared
ceiling preserve the two null and empty container distinctions. Levels
at or above that ceiling reach the same required Struct, with child
nullability checked separately. The first mismatch retains the
column paths, page ordinals, original absolute header offsets and
chunk slot ordinals of the available slots. The refusal proof
retains both independent chunk witnesses and the matched prefix.

Both child reconstructions use the existing checked LIST-path
inverse. Row and LIST merges check equal lengths before pairing.
Projecting either signed child from the merged rows restores its
entire original ordered trace, including every repetition, definition
and signed word. The group theorem retains the original row count
and both original column witnesses. `readAll` keeps footer order.

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
