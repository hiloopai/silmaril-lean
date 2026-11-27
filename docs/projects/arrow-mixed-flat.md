# Mixed-flat Arrow IPC V5 RecordBatch

`Arrow.MixedFlat.readBatch` consumes three caller-paired slices for a
bodyless little-endian Schema, RecordBatch metadata, and body. It admits
nullable or required Int32, Utf8, BinaryView and Utf8View fields and
returns the explicit batch row count and ordered field/column
observations. Compression, dictionaries, nested fields and
temporal types are outside this profile.
[Pinned Arrow 26.0.1 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[RecordBatch IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Message.fbs)

Every field consumes one node. Int32 takes two descriptors and Utf8 takes
three. A view takes two descriptors plus its own signed nonnegative count
of additional descriptors. Only views consume count entries, in Schema
order, including entries equal to zero. The metadata reader checks the
node and count cardinalities and per-view and total count limits. It
checks the resulting descriptor cardinality before reading descriptors.

The binder checks the common row count and nullability against every
node, and checks the entire ordered descriptor list against the
immutable body before slicing. Column decoding uses the existing
primitive bitmap, offset and value readers and the existing nullable
view slot readers. The batch uses configured row and cell budgets, and
views also use their per-column buffer and observed-value byte budgets.
Plan and column errors carry zero-based Schema field indices. Negative
or over-limit count diagnostics instead carry the zero-based position in
the count vector, which contains only view entries.
[Reader and planner](../../Silmaril/Formats/Arrow/MixedFlat/Defs.lean)

`Assignment.exact` reconstructs the input fields, nodes, counts and
descriptors in order from the plan. `Group.shape` ties each field to its
node length, count presence and descriptor width. `Plan.ordered_disjoint`
proves ordered non-overlap across arbitrary descriptor positions, and
`Plan.buffer_exact` identifies the exact body bytes for each assigned
descriptor. `Plan.readGroups_fields` preserves the declared field order
on successful column decoding. `readBatch_shape` relates the returned
Schema order and row count to the checked metadata.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Thms.lean)

The independent PyArrow 26.0.1 fixtures have two view columns, with
counts `[2, 1]`, `[1, 2]` after reordering and `[0, 0]` for a zero-row
batch. The pinned Linux x86-64 CPython 3.14 wheel has SHA-256
`7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814`.
The generated Schema, RecordBatch and body slices are checked in as Lean
bytes. Lean checks ordered values and rejects missing, excess, negative
and over-budget entries, cross-field overlap, mismatched nodes and a
same-total count swap that deprives one field of a referenced buffer.
[Generator](../../scripts/arrow-mixed-flat/fixtures.py) ·
[Lean fixture checks](../../Silmaril/Formats/Arrow/MixedFlat/Examples.lean)

## Modern V5 streams

`Arrow.MixedFlat.Stream.read` admits the first Schema once and checks each
RecordBatch with the shared continuation-envelope and body readers. Each
batch observation retains its envelope offset, padded metadata size, and
declared body length. These determine the metadata and body slices on
the original carrier and the next envelope offset. The reader keeps each
zero-row batch and requires explicit EOS at the carrier end.

After the Schema, typed errors carry the zero-based batch index. The
stream checks its running row and cell budgets before decoding each new
batch. Column failures retain their field index within that batch.
[Reader](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Defs.lean)

`Stream.read_iff` characterizes the ordered frames through exact EOS.
`Stream.RecordWire.ranges` gives the exact body and metadata windows
for admitted envelopes, and `Stream.read_batch_results` proves that
standalone batch decoding over those ranges recovers the ordered stream
observations.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Thms.lean)

The same pinned PyArrow wheel emits a stream with batch sizes
`[4, 0, 2]` and a schema-only stream. It reads the first two batches of a
derived fixture and rejects the truncation in the third body. Lean
checks the exact ranges and nullable values and distinguishes late body
truncation, envelope truncation, a corrupt view slot, budget exhaustion,
missing EOS and trailing bytes.
[Stream fixture generator](../../scripts/arrow-mixed-flat/stream_fixtures.py) ·
[Lean stream guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Examples.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.MixedFlat.Thms +Silmaril.Formats.Arrow.MixedFlat.Examples \
  +Silmaril.Formats.Arrow.MixedFlat.Stream.Thms +Silmaril.Formats.Arrow.MixedFlat.Stream.Examples
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-mixed-flat/Axioms.lean
python3 -I scripts/arrow-mixed-flat/fixtures.py
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

## Indexed V5 files

`Arrow.MixedFlat.File.readIndex` checks both `ARROW1` words, padding and the
footer range on one immutable source. It uses the shared V5 footer parser
and requires exact agreement with the embedded Schema. Aligned record
blocks occupy contiguous ranges in footer order, followed by the modern
EOS immediately before the footer. The checker validates the entire index
before any RecordBatch is decoded. [Pinned File.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/File.fbs)

`Index.readAt` validates the selected continuation prefix and Message
lengths against the footer. It uses the same per-batch row, cell and view
budgets as standalone decoding. An absent entry gives `none`, while a
bad record carries its zero-based footer index. Each call decodes only
the selected record, so errors in later records are reported when those
records are read. The API uses a finite in-memory source and a bounded
footer list. Stream-wide cumulative budgets apply to the stream API.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/File/Defs.lean)

`readIndex_exact` recovers the checked footer, Schema and EOS. `Index.block_range`
and `Index.block_order` prove alignment, extent and nonoverlap. `Index.readAt_exact`
identifies the selected entry, exact source octets and the same standalone
`MixedFlat.readBatch` result. `Index.readAt_sequential` equates lookups with
the corresponding observations of a successful ordered traversal, including
empty batches and absent entries. [Theorem header](../../Silmaril/Formats/Arrow/MixedFlat/File/Thms.lean)

The pinned PyArrow producer emits and independently opens files with row
counts `[4, 0, 2]` and `[]`. Their SHA-256 digests are
`efec769981c07a0c25fbaff56dc7af79ee9facfbda14a9099a52b89b7287516a` and
`ca999237b082b55fae3bc82d0ed7339bd66898ceaf92b90a016ee11fa404c8a8`.
Lean compares indexed values with the independently pinned stream and
checks malformed footer ranges, schema disagreement, missing EOS and
indexed length mismatches. [File fixture producer](../../scripts/arrow-mixed-flat/file_fixtures.py) · [Lean file guards](../../Silmaril/Formats/Arrow/MixedFlat/File/Examples.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.MixedFlat.File.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Axioms
python3 -I scripts/arrow-mixed-flat/file_fixtures.py
```

## Checked Int32 and BinaryView RecordBatch writer

`MixedFlat.Writer.emit` takes one Int32 column, one BinaryView column, an
explicit common row count, and a choice of field order. Names and
nullability come from the input. Each field may be nullable or required.
The result contains V5 RecordBatch metadata bytes, their exact metadata
AST, and the aligned body. A reader supplies the field declarations in
the same order because a RecordBatch Message carries no Schema.

The writer reuses the two physical encoders and packs their buffers in
field order. It writes an explicit signed 64-bit count for the view,
zero for inline-only and empty columns and one for a column with external
values. It checks lengths against the common row count and enforces the
configured field, row, cell, view and byte limits. The padded body
budget is checked before packing. It certifies the output by parsing the
RecordBatch metadata, comparing the exact AST, and running
`MixedFlat.readParsed` and comparing the ordered column observations.
This entails a full read and value comparison. All byte limits apply to
this batch.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Writer/Defs.lean)

`Wire.metadata_extent` gives the exact serialized metadata size.
`emit_layout` fixes the row count, field nodes, view count, aligned body
and exact packed descriptor windows. `emit_assignment` gives the
reader's exhaustive schema-order plan. `emit_partition` identifies the
two descriptor groups and the view's count in either field order.
`emit_readback` recovers the exact metadata, row count and ordered
nullable values. BinaryView equality compares octets per present cell.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Writer/Thms.lean)

Pinned PyArrow 26.0.1 reads four standalone Lean-emitted RecordBatch
Messages with independently supplied field declarations. It checks the
row and null counts, descriptor order and extents, signed variadic
count vector, and ordered values. Cases cover both field orders, signed
Int32 extremes, nullable and required columns, zero rows, and the 12/13
byte threshold. Lean guards reject inconsistent row counts, nulls in
required fields, and exhausted body, metadata and data-buffer limits.
The fixture driver supplies one modern continuation prefix for PyArrow.
The library API emits the metadata and body of a single RecordBatch.
[Oracle](../../scripts/arrow-mixed-flat/writer_fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/MixedFlat/Writer/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Writer.Examples +Silmaril.Formats.Arrow.MixedFlat.Writer.Axioms'
python3 -I scripts/arrow-mixed-flat/writer_fixtures.py --out /tmp/arrow-mixed-flat-record-writer
```

## Checked Int32 and BinaryView stream writer

`MixedFlat.StreamWriter.emit` takes one `Schema` and a list of
`BatchInput` values. The schema declares the Int32 and BinaryView names,
nullability, and field order. Each batch supplies its explicit row count,
ordered nullable Int32 slots and ordered nullable `KBytes` slots. A
schema-only stream retains both declarations. A zero-row batch still emits
one RecordBatch and consumes one unit of the batch-count limit.

The writer emits one little-endian V5 Schema, then reuses the standalone
writer for every RecordBatch. It uses modern continuation framing and
terminates with explicit EOS. Running row and cell budgets are checked
before record encoding. Their failure names the zero-based batch index.
Standalone writer failures keep both the batch index and any field
index. IPC body and metadata byte caps bound individual frames, while the
column byte caps apply in each batch. The whole stream has a batch-count
cap and cumulative row and cell caps.

Successful emission reads back the complete stream with
`MixedFlat.Stream.read` and compares the exact field declarations and
ordered values. This adds a stream decoding and comparison pass to the
standalone writer's per-batch checks.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/StreamWriter/Defs.lean)

`Wire.schema_extent` gives the precise Schema metadata extent.
`emit_readback` proves exact schema ordering and equality of nullable
observations, with BinaryView cells observed by their octets.
`emit_batch_rows` preserves the outer batch count and every row count.
`emit_wire` ties those observations to the checked source ranges and EOS
at the end of the carrier.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/StreamWriter/Thms.lean)

Pinned PyArrow 26.0.1 reads five Lean-written streams. The cases include
both orders with row counts `[4, 0, 2]`, required fields, a schema-only
stream and the same schema with one empty batch. The oracle checks both
names and nullability, every value, every modern prefix and aligned body
extent, and final EOS. Lean guards exercise indexed record and budget
errors, and the existing PyArrow-generated mixed stream still serves as
an independent inbound control.
[PyArrow oracle](../../scripts/arrow-mixed-flat/stream_writer_fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/MixedFlat/StreamWriter/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Examples +Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_writer_fixtures.py --out /tmp/arrow-mixed-flat-stream-writer
```

### Ordered INT32, BinaryView and Utf8View writer

`MixedFlat.OrderedWriter.emit` accepts an ordered schema of INT32,
BinaryView and Utf8View fields under the existing IPC caps. The text
constructor accepts nullable Lean strings, and the binary constructor
accepts nullable octets. The checked schema requires the matching kind
at each field position. Each view column owns its local buffer indices
and contributes one count word, including zero for an inline-only or
empty column. The mixed reader certifies the original ordered strings,
octets and batch counts through exact EOS.

`compile_utf8_wire` gives the exact nullable string readback from one
view's own buffers. `compile_utf8_count` measures external payloads by
encoded byte length. The PyArrow 26.0.1 comparison interleaves both
view kinds with INT32 and checks `[4, 0, 3]` rows. The Lean output has
view count vectors `[0, 1, 1, 0]`, `[0, 0, 0, 0]` and `[1, 0, 0, 1]`.
The comparison includes nulls, empty values, composed and decomposed
text, embedded NUL, and non-UTF8 BinaryView values.

The opt-in `emitSchemaWith` and `emitRecordWith` helpers also support
plain Utf8 for callers that admit it. `compile_plain_utf8` gives the
three primitive parts and the signed offset bound, with no variadic
count. The default ordered stream entry points retain their existing
profile. The plain Utf8 guards interleave two plain columns with Int32
and Utf8View, and verify the exact field order, descriptors and values.

For a complete stream, pass that profile explicitly to
`MixedFlat.OrderedWriter.emitWith`. For example, a caller with a
declared `fields` list can pass `fun signature => signature == fields`
to admit just that list. The writer checks the same profile at the
Schema and RecordBatch boundaries. Plain Utf8 keeps its primitive
descriptor, while Utf8View retains its view descriptor and count word.
`emitWith_schema_eos` recovers the exact original Schema and end offset,
and `emitWith_pull_exact` aligns the native pull trace, including empty
batches, to the ordered input observations through EOS. The default
`emit` and `serialize` still apply their original admission predicate.

The pinned PyArrow stream oracle checks both producer directions for
repeated plain Utf8 fields interleaved with both view kinds and Int32.
It covers null, empty and multibyte strings, batch row counts of
3, 0 and 2, a schema-only stream, and one explicit empty batch.
[Plain Utf8 stream oracle](../../scripts/arrow-mixed-flat/plain_utf8_stream_oracle.py)

[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/OrderedWriter/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/OrderedWriter/Thms.lean) ·
[Mixed-view oracle and hashes](../../scripts/arrow-ordered-view-writer/check.py) ·
[Legacy Parquet comparison](parquet-int32-byte-array-legacy.md#native-ipc-after-logical-scan)

```sh
lake build --wfail +Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Checks
python3 scripts/arrow-ordered-view-writer/check.py "$(mktemp -d)"
```

## Indexed files in a bounded carrier window

`MixedFlat.File.Window.readIndex limits carrier start stop` accepts an
explicit absolute window `[start, stop)` in an immutable `KBytes`
carrier. The window starts on an eight-byte boundary. The trailing magic
ends at `stop`. The caller supplies both bounds. Every footer block
offset is an absolute address from byte zero of the carrier. Lengths count
the original prefix, padded metadata and body extents.

The reader checks the carrier and bounds first. It locates the footer
trailer within the bounded window, checks both magic words and leading
padding, then parses the footer and embedded Schema on the original
carrier. The two supported Schema declarations must match exactly.
The bodyless Schema ends at the first block's start. Contiguous aligned
blocks in footer order occupy the interval through the exact modern EOS
immediately before the footer. The reader checks the index before
selecting any batch.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Defs.lean)

`Index.readAt` decodes one selected block using the existing mixed V5
decoder. It checks the selected continuation prefix and compares
Message lengths with the indexed extents before slicing the metadata
and body. An absent entry returns `.ok none`. A malformed selected
record reports its footer index. Bytes in the carrier outside the window
cannot satisfy a declared file block range.

`readIndex_exact` recovers the original footer, matching embedded
Schema and EOS. `Index.footer_range` and `Index.footer_bytes_exact`
give the original footer window. `Index.block_ranges` proves the selected
prefix, metadata and body fit inside the caller window and end before
EOS. `Index.block_order` gives physical order and non-overlap.
`Index.readAt_exact` identifies the three original byte slices and
recovers the same ordered nullable observation from the standalone
mixed batch reader.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Thms.lean)

The pinned PyArrow 26.0.1 producer writes an Int32/BinaryView V5 file at
byte 64 and appends a suffix after the file. On the whole carrier,
`ipc.open_file(..., footer_offset=1354)` checks both Schema declarations
and reads the batches out of order with row counts `[4, 0, 2]` in footer
order. The pinned carrier SHA-256 is
`f1c55f598ee91bf522d50e582121f977ed4c62cda5be64026b95dcda0215e9ee`.
Independent PyArrow and Lean checks isolate an external-prefix failure
in the first record and a negative view length in the last record.
The other batches remain readable. Lean guards also exercise out-of-window
blocks whose bytes exist in the carrier, Schema disagreement, and malformed
prefix lengths and EOS.
[Producer and independent check](../../scripts/arrow-mixed-flat/window_fixtures.py) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Examples.lean) ·
[Pinned PyArrow wheel](../../tests/formats/arrow-ipc/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.File.Window.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Window.Axioms'
python3 -I scripts/arrow-mixed-flat/window_fixtures.py --out /tmp/arrow-mixed-window.bin
```

### Selected batch projection

After admitting a carrier-window index, use `Index.checkProjection` to
check zero-based column positions against the footer and
`Index.readProjectedAt` to read one batch with those positions.
`Relational.Scan.Projection` permits reordering and repetition. Its
positions refer to the original field declarations, including their
names, types and nullability.

The full selected batch passes the existing decode and budget checks
before projection. Corruption in an omitted column still produces the
original indexed source error. Other batches are unread. A missing
batch returns `.ok none`, and an explicit zero-row batch returns
`.ok (some observed)`. An empty projection keeps the original
`rowCount`, including for a nonempty batch. Output width is the width
of the caller's request, which may include repeated positions.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Projection/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Projection/Thms.lean)

The Lean checks use the same independently produced carrier with batch
counts `[4, 0, 2]` at origin 64. The pinned PyArrow 26.0.1 oracle
checks repeated and reordered positions, zero-width row counts, and
selected corruption with readable neighbors after full batch validation.

```sh
lake build --wfail +Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Axioms
python3 -I scripts/arrow-mixed-flat/window_fixtures.py --out /tmp/arrow-mixed-window.bin
python3 -I scripts/arrow-mixed-flat/window_projection.py /tmp/arrow-mixed-window.bin
```

### Agreement with strict file traversal

For the full carrier window `[0, input.len)`,
`Index.readProjectedAt_strict` compares both readers on the same immutable
input and limits. Successful strict and window admission identify the same
footer. After every strict record decodes in footer order, an indexed
projection at ordinal `n` agrees with the strict observation at that
ordinal. Each output position has the exact descriptor and column selected
by the projection. The batch row count is explicit, so a four-row batch
still has four rows at width zero, an empty batch stays present, and a
missing ordinal returns `.ok none`.

The proof assumes successful strict traversal. The damaged-prefix guard
shows that a valid suffix batch can still be read by index when a prior
record fails strict traversal. The event-scan comparison separately
requires an alignment witness between strict observations and events.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Projection/Strict/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/File/Window/Projection/Strict/Examples.lean)

The pinned PyArrow 26.0.1 producer reproduces the original multi-batch and
schema-only fixtures. Its file and embedded stream readers agree on ordered
nullable columns at positions `[3, 0, 3, 1]`, including the repeated view
column. With no projected columns the batch row counts are still
`[4, 0, 2]`. The schema-only file has no batches.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Strict.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Strict.Axioms'
python3 -I scripts/arrow-mixed-flat/file_fixtures.py
```

### Strict file events

`MixedFlat.File.Events.read` eagerly decodes the strict file into the
existing Arrow event model. The source schema contains the exact ordered
footer declarations, and the trace contains one aligned event per footer
entry followed by EOS. Explicit empty batches remain in the trace. A
zero-column batch carries its row count without allocating cells.
Primitive slots, BinaryView octets and Utf8View strings retain their
values and nulls.

File admission and per-batch decoding use the existing limits. The adapter
also checks the running total rows and cells after decoding each candidate
batch and before retaining it. This may decode one candidate beyond the
aggregate observation budget under the per-batch limits. Byte budgets
apply per message or column as in the existing decoder. Admission or
decode failure returns the original file error, with a footer ordinal for
a failed record. An aggregate limit error carries the candidate's
ordinal. Each failure is atomic and yields no schema or prefix trace.

`Events.read_exact` derives the alignment from the strict decoder's field
and slot-count laws. `Events.read_projectedAt_scan` uses this alignment to
compare the existing keep-all event scan with indexed projection over the
full carrier window. For every ordinal it identifies the same presence,
explicit row count, output width, ordered descriptors and nullable slots.
The law applies after a successful eager read. An independent indexed
read can still reach a valid batch in a damaged file.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/File/Events/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/File/Events/Thms.lean)

The Lean guards use the original pinned mixed and schema-only files and the
existing pinned zero-column file with counts `[3, 0]`. They compare
indexed reads with the actual event scan at repeated and empty positions,
and exercise a late wire error and both aggregate budget errors.
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/File/Events/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.File.Events.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Events.Axioms'
python3 -I scripts/arrow-mixed-flat/file_fixtures.py
python3 -I tests/formats/arrow-ipc/file_fixture.py --regenerate
```

### Pull events from a strict file

`MixedFlat.File.Events.Pull.reader` implements the existing
`Arrow.Events.BatchReader` protocol. A successful open validates the
strict file index and exposes its footer schema. Each `next` checks
the next ordered footer block using the same single-record step as the
eager reader. It delivers that batch, including an explicit empty batch,
or returns the original record error with its zero-based ordinal. Each
cursor tracks the running accepted rows and cells independently. The
candidate's existing per-batch checks run before its aggregate check.
The cursor signals EOS on a call after the final batch.

`Pull.readAll` uses the generic pull driver with enough calls to reach
EOS. After a successful open, a late failure becomes `.readError` and
the trace retains the batches already delivered. An admission failure
appears as the outer error. The generic driver's caller-supplied fuel
can also stop early with `.closed`. The cursor retains the entire
immutable file carrier and the remaining footer entries. Pulling one
batch at a time bounds the number of records decoded per call. The
collecting driver retains all delivered events in its result.

`Pull.readAll_eager` gives exact schema and batch agreement at EOS.
`Pull.readAll_failure_exact` identifies the completed strict footer
prefix with its aligned events and the next failed block. The cause is
either the original strict record error or the aggregate limit failure
after decoding the candidate. The eager reader returns that same error.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/File/Events/Pull/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/File/Events/Pull/Thms.lean)

The guards exercise the original mixed file `[4, 0, 2]`, schema-only
absence, and the pinned zero-column file with row counts `[3, 0]`.
A third-record length fault retains the first two batches and their
exact values. The two running budget controls retain the same prefix.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Axioms'
python3 -I scripts/arrow-mixed-flat/file_fixtures.py
python3 -I tests/formats/arrow-ipc/file_fixture.py --regenerate
```

### Pull events from an IPC stream

`MixedFlat.Stream.Events.reader` opens the checked Schema from an
immutable IPC stream carrier. Each `next` checks one original envelope
and uses the existing mixed stream record decoder. A zero-row batch
still yields an event, and a zero-column event carries its explicit row
count. The cursor holds the next byte offset, zero-based ordinal after
the Schema, remaining batch count, and running accepted rows. The
existing decoder checks the framing, metadata, body, and row and cell
limits in their existing order.

A post-open failure supplies the attempted ordinal, original carrier
offset and original eager error cause. The collector retains every
event delivered before the failure. EOS requires a complete modern
continuation/EOS frame at the end of the carrier. EOF without that
frame is a truncated envelope. Extra bytes after EOS are an error.
`readAll_exact` relates successful collection to the eager reader's
ordered batches and identifies the delivered prefix, stopping offset
and cause on failure. `Prefix.ordinal` counts empty batches as one
message each.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Events/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Events/Thms.lean)

The cursor retains the original carrier in memory. Each direct call
decodes one record and the collecting driver retains delivered events
in its result. This API consumes an already available carrier.

The pinned PyArrow 26.0.1 producer writes the mixed `[4, 0, 2]`,
schema-only, and zero-column `[3, 0]` streams. The Lean guards
distinguish a third-record body truncated at byte 1743, a missing EOS
after all three batches at byte 1744, and data after explicit EOS.
Separate guards exercise envelope and body caps, batch count, and
running row and cell budgets.
[Producer](../../scripts/arrow-mixed-flat/stream_fixtures.py) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Events/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Incremental IPC framing

`Arrow.Framing.Incremental.start` starts at an absolute byte offset.
Supply ordered `KBytes` fragments to `feed`. A `.wait` consumed the
whole fragment and awaits another. An `.advance` or `.frame` returns
the pending state and the unused suffix. Feed that suffix before
taking another fragment, including an empty suffix that completes
a zero-length body. Each emitted frame carries its absolute prefix
offset and its exact metadata and body bytes.

Call `finish` after processing all input. A pending prefix, metadata
or body request becomes a typed truncation with its absolute request
offset. Success requires explicit modern EOS. A nonempty suffix in
the same fragment or a later fragment fails at the first tail byte.
The framer checks continuation, alignment, the common V5 Message
table and the existing per-message metadata and body caps. It accepts
Schema and RecordBatch envelopes. Schema order, typed payloads and
stream-wide batch, row and cell limits belong to the downstream reader.

The cursor holds only the current request and, while collecting a
body, the completed metadata for that frame. The caller owns unused
suffixes and delivered frames. Completed metadata is repacked for
the Message table check. The caps bound logical frame bytes. This
API provides no allocation or runtime bound for fragmented ropes.

The feed law preserves contiguous original byte windows for each
ordered fragment and suffix. Each emitted frame agrees with the
immutable envelope and body parsers and carries the original
metadata octets. The finalization law identifies the EOS at exact
exhaustion. Guards compare the checked ranges and bytes for cuts
through each framing stage in the pinned PyArrow stream, including
one-byte fragments, a nonzero origin, and zero-body records.
[Definitions](../../Silmaril/Formats/Arrow/Framing/Incremental/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/Framing/Incremental/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/Framing/Incremental/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.Framing.Incremental.Examples +Silmaril.Formats.Arrow.Framing.Incremental.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Incremental mixed events

`MixedFlat.Stream.Incremental.start` fixes the limits and starts at byte
zero. `feed` publishes the checked Schema once and yields an aligned event
for each completed RecordBatch, including an empty batch. A zero-column
batch retains its explicit row count. The returned ranges refer to the
original stream. As with incremental framing, process the returned suffix
before reading the next fragment, including an empty suffix. An error
ends the call sequence and leaves the schema and batches from prior
replies available to the caller.

The framer applies the existing per-message byte limits. The typed
decoder uses the complete mixed Schema and RecordBatch decoders and checks
the running batch, row, cell, and view data-buffer counts before publishing
a batch. The view data-buffer count sums the variadic count words as declared
by the schema. The per-view and per-batch count caps still apply. The
additional stream-wide count cap is separate from the per-message byte
limits. The ordinary immutable readers retain their existing limits.

An EOS reply is provisional. Call `finish` after the last supplied byte
to certify exact exhaustion. Missing bytes at finalization produce a
framing failure, and bytes after EOS report the first tail offset. A late
typed failure carries the original zero-based batch ordinal, message
offset, and typed decoder cause. The incremental path finishes framing
the candidate before typed decoding, so framing can fail before a typed
check that the immutable reader would attempt earlier.

The cursor holds the admitted field list, counters, and one pending frame.
It repacks the completed metadata and body for typed decoding. The caller
owns pending suffixes and published events. The byte limits bound the
logical sizes of the frame parts. The API does not bound allocation or
time for fragmented ropes.

`open_agrees`, `steps_agree`, and `finish_agrees` link actual calls to
the immutable Schema, exact ordered pull prefix, and original EOS.
`complete_agrees` gives the original immutable eager result, including
exact record ranges. `complete_pull_agrees` gives the exact immutable
pull trace through EOS. The reference carrier in these laws is represented
as one packed leaf. The incoming fragments can have arbitrary
well-formed rope shapes and ordered cut points. Guards compare exact
values and ranges for one-byte and adversarial splits of the pinned
PyArrow streams, including a late typed failure and late truncation.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Ordered writer and incremental schedules

`MixedFlat.Stream.Incremental.Portable.schedules_equivalent` compares
two successful schedules under the same explicit incremental limits.
For well-formed carriers with identical octets, it gives equal final
offsets, absolute RecordBatch ranges and keep-all projected traces.
The projection can select, reorder, repeat or omit fields. Zero-width
rows and explicit empty batches remain separately observable.

`Portable.Completed` records actual successful feed calls and finish.
The laws use a packed immutable reference of those same octets and
the existing eager and pull agreement laws. `Portable.writer_readback`
relates any such schedule to an ordered writer result after
`checkWriterReadback` confirms the expected fields and batch observations
on that reference. This offline check compares the same bytes in the
proof representation. The live cursor continues to consume fragments
and apply its configured stream-wide caps.

One-byte and uneven schedules exercise both the checked writer and
independently emitted PyArrow 26.0.1 streams. Three BinaryView positions
use count vectors `[1, 0, 1]`, `[0, 1, 0]`, and `[0, 0, 0]`. The
projection `[3, 0, 3, 1]` retains the repeated value and nullable
octets in row order. The separate zero-width stream has batch row
counts `[3, 0]`. The mixed fixture succeeds at the stream-wide
data-buffer cap of three and fails at the second batch with a cap of two.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Portable/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Portable/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Portable/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Axioms'
python3 -I scripts/arrow-mixed-flat/ordered_incremental_fixtures.py
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Observable failure after EOS

`Incremental.Failure.TailFailure` describes a finite schedule with a
checked Schema, a delivered record prefix and a terminal feed error.
The fragments are well-formed windows of a complete reference carrier
under fixed limits. The final call supplies a byte after EOS. It can
complete the EOS marker and supply the byte in the same fragment, or
follow provisional EOS from an earlier call.

`tail_exact` identifies the exact immutable successful pulls and their
absolute ranges, followed by the immutable trailing-data error. The
typed feed error retains the next record ordinal, the tail part, the
first tail byte offset, and the trailing-bytes cause. The immutable
pull reports the same ordinal at the EOS marker eight bytes earlier.
`schedules_tail_equivalent` compares the complete prefix and exact feed
cause across schedules that reach this failure on equal octets.
`tail_no_success` rules out successful finish for any complete schedule
over those same octets and limits. The offending call supplies no
successor cursor.

These comparisons apply to tails after a complete EOS. A source cutoff
uses `finish` and supplies its own declared end of input. A cutoff before
the actual tail is a different carrier. An incomplete request reports
its original part and truncation cause at finalization. Malformed input
fragments and feeder-specific refusals fall outside the admitted window
schedule. The wire metadata and body caps retain their own limit
diagnostics. Row, batch, data-buffer, and semantic decode failures retain
their typed causes. These failure classes have no cross-schedule theorem
in this slice.

The Lean guards append synthetic tail bytes to pinned PyArrow and native
ordered-writer output, and compare one-byte and uneven fragments. They
also exercise a synthetic body cutoff and a synthetic view-prefix edit
and compare the exact distinct causes across both schedules.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Finalization during a RecordBatch body

`Incremental.Failure.BodyCutoff.Run` describes the entire supplied prefix
ending strictly inside a planned RecordBatch body. The pending metadata
must pass the immutable mixed RecordBatch metadata check, declare the same
body length as the framing request, and have an available batch slot.
These conditions matter because the immutable reader can reject a batch
slot or typed metadata before reading the body. The incremental reader
reaches these checks after it has framed the complete body.

`wait_body` proves that a valid fragment leaving the body short returns
ordinary waiting. `body_cutoff_exact` identifies the finish failure at the
original body start and the immutable truncation at the original message
start, with the same next batch ordinal. Every complete preceding batch
and its absolute range replays in the original order. For schedules
over the same supplied octets and limits, `schedules_body_equivalent`
equates these prefixes and their exact typed finish causes.
`body_cutoff_no_success` excludes a successful finish on the same
supplied octets. Continuing the source before finish can complete the
batch and reach EOS.

The guards cut one byte short of the last body in native and pinned
PyArrow streams and compare one-byte and uneven schedules. They include
a cutoff exactly at the body boundary, resumption through EOS, and the
body-byte cap at the declared length and one lower. A batch-count
control exercises the distinct immutable batch-limit precedence.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyCutoff/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyCutoff/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyCutoff/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### External view prefix mismatch after complete framing

`Incremental.Failure.PrefixMismatch.Run` describes an admitted schedule
through a checked Schema, a complete published prefix, and a later
fully framed RecordBatch rejected at an external view slot. The
original metadata and body spans, batch slot, variadic count limits,
and running row and cell budgets are checked before the field decoder.

`feed_field_wire` recovers the original complete frame and the exact
field error from the terminal feed. `record_field_error` and
`field_terminal` transfer that cause to the immutable record and
stream readers. These laws also apply to other typed column causes
that surface after complete admission.

`prefix_mismatch_exact` replays every prior batch and its absolute range.
The terminal cause keeps the original batch ordinal, message offset,
field index and slot index. The trace ends with the error and has only
the previously published batches. `schedules_mismatch_equivalent`
compares two admitted schedules that reach the mismatch on the same
octets and limits. `mismatch_no_success` excludes a completed stream
on those octets.

The one-byte and uneven guards use synthetic four-byte edits to a
native BinaryView stream and the pinned PyArrow mixed stream. The
original frame extents and the EOS bytes are present in both inputs.
The batch, row and cell controls report their own earlier errors.
The incremental aggregate data-buffer cap also takes precedence
when lowered below the candidate total.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/PrefixMismatch/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/PrefixMismatch/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/PrefixMismatch/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Schedule agreement for typed field errors

`Incremental.Failure.Field.Run` covers any `MixedFlat.ColumnError` reached
after a checked Schema and a fully admitted RecordBatch. `field_exact`
recovers the rejected frame in the original carrier, replays every earlier
complete batch with its absolute range, and identifies the same indexed
cause in the immutable next-record read and eager stream read.
`field_pull_exact` gives the full immutable pull trace, including empty
batches and the terminal error. Only complete batches are published.

`schedules_field_equivalent` gives equal complete event traces, original
batch ranges, and exact typed causes for two admitted schedules that reach
a field error on the same octets and under the same limits.
`field_no_success` rules out successful finish on those octets.
`FieldFailureWire` retains the checks for the message and body extents,
metadata, available batch slot, running row and cell budgets, and
incremental aggregate data-buffer cap. Framing and metadata rejections
are outside this law. The immutable reader has its own limits and does
not enforce the incremental aggregate data-buffer cap.

The synthetic controls also exercise a native Int32 validity bitmap
inconsistent with its field node and an inline BinaryView padding octet
in the pinned PyArrow carrier. One-byte and uneven schedules both retain
the earlier complete batch and the explicit empty batch. The original
prefix mismatch and budget precedence controls still run.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Field/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Field/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/PrefixMismatch/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Field.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Field-node count rejection after complete framing

`Incremental.Failure.NodeCount` covers the shared typed metadata error
`MetadataError.nodeCount expected actual` after the incremental reader
admits the complete RecordBatch frame. `feed_node_count_wire` retains
the original envelope, metadata slice and checked body range.
`node_count_exact` replays the complete preceding batches and absolute
ranges, with the same metadata error in the immutable next read and
eager reader. `node_count_pull_exact` gives the full immutable pull trace,
including explicit empty batches. Admitted schedules that reach this
error on the same octets under the same limits agree on all published
batches, ranges and the exact cause. Those octets cannot finish successfully.

Both typed readers check the remaining batch slot before the node count
and apply the running row and cell budgets afterward. The incremental
reader also checks the body-byte cap during framing, before the typed
metadata parser. The immutable reader applies it after typed metadata
admission. The incremental aggregate data-buffer cap can stop an earlier
valid batch, while the immutable reader can continue to the node-count
error. These distinct outcomes and other metadata or framing errors are
outside the agreement theorem.

The guards shorten the last node vector in a native stream and the
pinned PyArrow 26.0.1 stream while preserving the declared frame extents.
Both one-byte and uneven schedules compare the same earlier batch and
explicit empty batch, and check the batch-slot, row/cell, body-byte and
aggregate data-buffer precedence cases.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/NodeCount/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/NodeCount/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/NodeCount/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Shared RecordBatch metadata parser rejection

`Incremental.Failure.RecordMetadata` generalizes the node-count laws
to any `MixedFlat.MetadataError` actually returned by the shared parser
for a completely framed record. The existing `NodeCount` API specializes
that result.

`decode_metadata_error_iff` identifies the ordering at the typed decoder.
A batch slot must be available, then the common metadata parser must
return the cause. This includes its own per-record count limits. A
metadata rejection wins over subsequent running row, cell and incremental
aggregate data-buffer checks at that record. Incremental framing can
still stop before typed metadata. An incremental-only budget can also
stop an earlier record. Later body layout, field decoding and unrelated
terminal failures are outside the theorem.

The wire witness keeps the original envelope, metadata slice and
checked body range. The immutable pull and eager readers preserve the
exact indexed cause. The pull trace contains every complete preceding
batch, including explicit empty batches, and the replay retains absolute
ranges. Schedules which reach a shared metadata rejection on the same
octets and limits give identical complete traces and prefix ranges.
Successful finish under those conditions is impossible.

Synthetic edits to the pinned PyArrow stream shorten the descriptor
vector, omit the variadic-count section, make a field-node length
negative, and exceed the shared per-record count limit. The node-length
case concerns the signed metadata field. Geometry that survives metadata
parsing and fails layout binding belongs to a later error class. Each
control compares one-byte and uneven schedules with immutable readback.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/RecordMetadata/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/RecordMetadata/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/RecordMetadata/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Shared RecordBatch body layout rejection

`Incremental.Failure.BodyLayout` covers a field-assignment error or a
malformed descriptor layout reported by the shared binder on a complete,
admitted RecordBatch. The wire witness retains the absolute frame
range, admitted metadata, and exact original body. It records the
available batch slot, accepted running row/cell checks and accepted
incremental aggregate data-buffer check before the binder rejection.

The immutable reader checks the envelope and batch slot, parses shared
metadata, then reads the declared body before checking running rows and
cells. The incremental reader completes framing, including the declared
body, before checking the batch slot and shared metadata. It checks its
stream-wide aggregate data-buffer allowance before running rows and
cells. Both readers check rows before cells and then invoke the shared
binder. A framing failure or a budget refusal can change which error is
observed. Those cases are outside this agreement law. Per-record count
limits in the shared metadata parser are separate from the incremental
aggregate allowance.

The laws preserve every preceding complete batch and its absolute range,
the full immutable pull trace, and the eager error. Admitted schedules
reaching a covered layout error on the same octets and limits preserve the
exact trace and cause. Successful finish is impossible under those
conditions.

Synthetic edits to the pinned PyArrow stream retain the complete frame
while making a node disagree with the row count or extending a descriptor
beyond the body. The one-byte and uneven controls preserve the prior data
and explicit empty batch. The budget controls show common row and cell
preemption, and the divergent incremental aggregate rejection.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyLayout/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyLayout/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyLayout/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Examples +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Admitted RecordBatch rejections

`Incremental.Failure.Admitted.Cause` gives one public sum for shared
metadata, layout and indexed column rejections. Each case retains its
existing wire witness. The common laws recover the exact preceding
records and absolute ranges, the original rejected frame, and the
immutable pull and eager causes. The zero-based rejection ordinal is
the number of complete published batches, including empty batches.
Admitted schedules that reach a covered rejection on the same bytes
under the same limits have equal traces, prefix ranges and terminal
causes. No schedule on those bytes under those limits can finish
successfully.

The parser coverage theorem starts with the body source, extent,
alignment and byte cap checked, fields and per-record rows within the
metadata caps, and the running row/cell check passed. The running bound
also implies the binder's current-batch row/cell bound. The remaining
binder errors are assignment and malformed descriptor layout.
After binding, the grouped reader returns only indexed column errors.
The metadata case retains any rejection returned by the shared parser,
including its per-record limit errors.

The sum excludes earlier envelope, body framing and EOS errors, schema
opening failures, batch-slot refusal, shared running-row/cell refusal,
and the incremental aggregate data-buffer refusal. These remain
observable in their original APIs with their own precedence. In
particular, the incremental aggregate allowance is checked before the
shared running row/cell limits, and the immutable reader has no matching
aggregate check.

A double-fault synthetic edit of the pinned PyArrow carrier includes an
invalid node and an out-of-body descriptor. The assignment error wins
before the global descriptor check in both immutable readers and in
one-byte and uneven incremental schedules.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Admitted/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/Admitted/Thms.lean) ·
[Lean guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Failure/BodyLayout/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.Axioms +Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Examples'
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

### Checked mixed-flat file writer

`MixedFlat.FileWriter.emit` writes a strict Arrow IPC V5 file from ordered
Int32, plain Utf8, BinaryView and Utf8View fields and batches. It reuses the ordered
record encoder, the primitive file writer's block packer, and the shared
File.fbs footer layout. The embedded Schema and footer carry the same
ordered names, kinds and nullability. The writer accepts schema-only
files, explicit empty batches, and nonempty zero-width batches.

The input row and cell totals are checked before encoding. IPC metadata,
body and per-record view limits apply at their existing scopes. The file
writer certifies the complete strict index and redecodes every original
block in footer order before returning bytes. It retains exact row
counts, nullable values, text, and BinaryView octets. A selected index
agrees with the corresponding observation from ordered readback.
`emit_block_offset` gives the original absolute offset as the end of the
embedded Schema plus the spans of every preceding record. `emit_events`
aligns the actual native file pull trace through EOS.

Plain Utf8 keeps its primitive descriptor in both schemas and uses
validity, signed 32-bit offsets, and data buffers. It contributes no
variadic count. Utf8View retains its distinct descriptor and count word.
The plain-text oracle interleaves repeated plain fields with Int32 and
both view kinds, including null, empty and multibyte strings. Dictionary
and nested fields are outside this writer profile.

The pinned little-endian PyArrow 26.0.1 oracle independently generates
mixed, schema-only, empty and zero-width files, then checks their exact
offsets and order. Lean reads those files and emits corresponding files.
PyArrow checks both the footer-indexed batches and their order in the
embedded message region.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/FileWriter/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/FileWriter/Thms.lean) ·
[PyArrow oracle](../../scripts/arrow-mixed-flat/file_writer_oracle.py)

```sh
lake build +Silmaril.Formats.Arrow.MixedFlat.FileWriter.Examples +Silmaril.Formats.Arrow.MixedFlat.FileWriter.Axioms
python3 -I scripts/arrow-mixed-flat/file_writer_oracle.py /tmp/arrow-mixed-file
```
