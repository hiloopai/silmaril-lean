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
group. This profile reads unindexed V1 and V2 data pages.
PLAIN columns independently admit UNCOMPRESSED, bounded Snappy, bounded
LZ4_RAW, single-member GZIP, or bounded single-frame dictionary-free
Zstandard according to its original footer metadata. Each keeps the
LIST-path byte, page, row, slot and codec bounds and reuses its
Compact framing, stored CRC, exact
Hybrid and signed word extents, and both header-inclusive totals.
V1 level sections have length prefixes and may continue live ancestry
across pages. Compressed V1 expands the complete body after checking its
stored-byte CRC. Its section offsets refer to the decoded body, and
the original frame's header and payload offsets remain absolute.
V2 uses the original raw sections selected by the header's repetition
and definition lengths. It decompresses only a flagged value suffix on a compressed
chunk. A false flag keeps the original raw suffix. V2 independently
checks slot, row and null counts and closes both boundaries, even for a zero-slot page.
The two columns can use different codecs, page versions and row cuts.
`Reader.ColumnWire.v1_page` and `Reader.ColumnWire.v2_page` recover
the original frame at its absolute header offset and expose the
LIST-path wire witness at the codec selected by the original chunk.
Each UNCOMPRESSED child may also declare a leading PLAIN dictionary
and use RLE_DICTIONARY data pages with page-local PLAIN fallback.
Dictionary and data anchors, signed entries, counted Hybrid indices
and both header-inclusive totals bind to that child's original chunk.
An empty dictionary may serve a page with zero physical values.
Slot and refusal ordinals include the leading dictionary when present.
The native writer emits UNCOMPRESSED PLAIN V1.

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
Native Events, the native writer and both strict IPC bridges support
both element nullability choices.
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
schema admission. The original V2 and Snappy probes verify successful
reconstruction from their original frames.
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
completed group prefix under full and empty Events.
[Optional-element fixture pins](../../scripts/parquet-recursive-two-list-struct-optional-element-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-optional-element-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-optional-element-oracle/check.py
~~~

The V2 oracle uses genuine PyArrow inputs for all sixteen LIST and
child nullability choices with each Struct nullability. Labeled
reframes exercise different V2 cuts, mixed V1/V2 pages with legal V1
continuations, and a physical zero-row V2 group. Independent inspection
checks original CRC, raw level sections, counters and signed slots for
both children. PyArrow and raw IPC inspection verify native Events
observations through the strict IPC bridge under both selections.
The refusal cases check late shared Struct presence, illegal boundary
transitions, V2 counters and extents, CRC and output-budget precedence.
The original uncompressed dictionary probe decodes successfully.
[V2 producer and fixture pins](../../scripts/parquet-recursive-two-list-struct-v2-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-v2-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-v2-oracle/check.py
~~~

The Snappy oracle checks genuine PyArrow V1 and V2 sources with both
Struct nullabilities, both signed width orders, independent child
nullability and per-child codec selection. The labeled reframes use
different child codecs and page cuts or store a raw V2 value suffix.
Independent Snappy, Compact, Hybrid and signed-word inspection checks
the original frame payloads, decoded bytes, level spans, CRC and both
header-inclusive totals. Full and empty projections retain ordered
group counts through exact Arrow IPC EOS. Late stored CRC, malformed
and trailing payloads, declared extents, byte bounds and footer totals retain an
original typed failure and the preceding complete group. The oracle
also checks compressed dictionary refusal at encoding admission and reads the original GZIP probe.
[Snappy producer and fixture pins](../../scripts/parquet-recursive-two-list-struct-snappy-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-snappy-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-snappy-oracle/check.py
~~~

The codec oracle checks genuine PyArrow LZ4_RAW, GZIP and Zstandard
files in both page versions, both Struct nullabilities and both
signed width orders. PyArrow also produces a file whose sibling
chunks have different codecs. A labeled reframe combines independent
codecs and page cuts, including V1 continuations, and matches the
uncompressed reference through exact IPC EOS. The original wire
checks cover both footer totals, stored-body CRC, level coordinates
and exact decoded values using pinned liblz4, libzstd and zlib.
False-flag V2 suffixes bypass even exhausted GZIP and Zstandard
codec budgets. Typed refusals cover legacy LZ4 IDs, framed LZ4 bodies,
GZIP trailers and extra members, Zstandard dictionary IDs and extra
frames, and compressed Parquet dictionary encoding. Late payload and shared
topology refusals retain their original positions and complete group
prefix under both projections, including with exhausted IPC budgets.
[Codec producer and fixture pins](../../scripts/parquet-recursive-two-list-struct-codecs-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-codecs-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-codecs-oracle/check.py
~~~

The dictionary oracle checks genuine PyArrow UNCOMPRESSED files in
both page versions and signed width orders. It covers required and
optional Structs, null Structs beside present all-null Structs,
per-child dictionary selection, genuine PLAIN fallback, and empty
dictionary and zero-value index lists. The labeled mixed-version reframe
retains distinct original signed tables and independent child cuts.
An uncompressed dictionary child also reads alongside a Snappy PLAIN
sibling. Independent Compact, Hybrid and signed-word inspection binds
the frames, entries, index lists and selected child slots. Late index,
dictionary CRC, data-anchor and shared-topology errors preserve their
original coordinates and completed group prefix through both Events
and strict IPC selections under exhausted target budgets. A late
compressed dictionary exercises the existing admission refusal.
[Dictionary producer and fixture pins](../../scripts/parquet-recursive-two-list-struct-dictionary-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms +Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-struct-dictionary-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-struct-dictionary-oracle/check.py
~~~
