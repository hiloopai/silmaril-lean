# Checked Arrow LargeUtf8 streams

Import `Silmaril.Formats.Arrow.LargeUtf8.Stream.Defs` for one flat
little-endian V5 LargeUtf8 field (Schema.fbs tag 20). `LargeUtf8.Stream.read`
retains the exact name and nullability, ordered batches, original frame
ranges and exact EOS. The caller chooses modern continuation framing or the
legacy signed-length profile for the entire carrier. Explicit EOS must
exhaust the input. A zero-row RecordBatch consumes a batch slot. Schema-only
input has no record frames.

Each record has one node and three ordered descriptors for validity,
signed little-endian i64 offsets and data. The reader shares checked slot
geometry with LargeBinary. The initial word is required even for zero rows.
Each adjacent pair must be nonnegative, nondecreasing and contained in the
original data descriptor. Validity must cover the declared rows and agree
with the declared null count and nullability. The existing per-message
limits and stream batch cap apply.

Present slots are checked for UTF-8 and returned as exact strings. A present
empty interval yields an empty string. As in plain Utf8, the reader checks
offsets under a null slot and returns null without inspecting the slot's
bytes as text. The LargeBinary reader continues to observe opaque octets.
Post-schema failures carry the original record ordinal, absolute frame byte
offset and typed cause. Invalid UTF-8 also identifies the original slot.

`LargeUtf8.Stream.read_sound` and `record_octets` bind the metadata and body
to their exact source windows. `LargeUtf8.slot_octets` identifies the two
original i64 words and the selected value span, proves UTF-8 validity for
present values, and identifies their exact re-encoded octets.
`LargeUtf8.Stream.read_failure` records the checked preceding frames and
the precise failing attempt. The reader returns a complete observation
after exact EOS.

Little-endian PyArrow 26.0.1 writes and reopens both pinned producer streams
and schema-only companions. The fixtures cover sliced input, multibyte
characters, embedded NUL, null and present empty slots, and an empty record.
The third producer record has a one-byte span under a null. Synthetic
controls distinguish inconsistent validity, a negative offset under null,
an offset past the data descriptor, and invalid UTF-8 in a present slot.
They also confirm that the same invalid byte under the null slot leaves
the observation unchanged.

- Modern SHA-256 `05ea324892d22c35a55893f8b2081e4687b34869374a36cf6ee2bd48dc4b66a5`
- Legacy SHA-256 `0d959e375bc54c26b785ec1f06b3e13b6995516bc52a4cc41b995a07f440797f`

```sh
python scripts/arrow-large-utf8/stream_fixture.py
lake build --wfail Silmaril.Formats.Arrow.LargeUtf8.Stream.Examples Silmaril.Formats.Arrow.LargeUtf8.Stream.Axioms
```

## Canonical modern writer

Import `Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs` and call
`LargeUtf8.StreamWriter.emit limits field batches`. The input declares one
flat LargeUtf8 field and a list of nullable string columns, one per batch.
The writer uses Schema.fbs tag 20 and modern V5 continuation framing. Before
encoding the string bytes, it checks the schema metadata extent and field and
batch counts, then checks each record's rows, nullability, signed i64 offset
extent, padded body size and metadata extent. Body, row and metadata limits
apply per message at the corresponding scope. The batch count applies to
the whole stream.

The three buffers hold the validity bitmap, signed little-endian i64 byte
prefix sums and concatenated UTF-8. Null and present empty slots repeat the
current offset, with their validity bits distinguishing them. A zero-row
record has the initial offset word. Empty input emits the schema and EOS
with no record. The writer materializes the admitted stream and certifies it
with the complete modern reader. `LargeUtf8.StreamWriter.emit_readback`
preserves the exact field, nullable strings and ordered batch boundaries,
including original readback windows through EOS and a canonical wire
witness for the encoded buffers.

The pinned writer oracle independently opens four Lean-generated streams
with PyArrow 26.0.1. It checks the exact descriptor, ordered rows, byte
prefix sums, payload and validity buffers, record envelopes and EOS. Its
SHA-256 checks pin nullable multibyte input with an empty batch, required
input, a schema-only stream and a stream with one explicit empty batch.

```sh
lake build --wfail Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Examples Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Axioms
python scripts/arrow-large-utf8/stream_writer_oracle.py /tmp/arrow-large-utf8-writer
```

## Events source and sink

Import `Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Defs` for the
standard `Arrow.Events.BatchReader` and the modern sink. The reader
opens the schema once, retains the original immutable carrier and
decodes each next frame in order. `readAll` pulls far enough to check
exact EOS or the first error. An explicit empty batch consumes a pull
and remains in the trace. An open error has no trace. A late read
error retains the completed batches and carries the original record
ordinal, absolute offset and typed cause, including the slot for
invalid UTF-8.

The sink consumes a complete one-field trace ending in EOS. It
materializes a modern V5 stream with the checked LargeUtf8 writer.
`emit_events` proves exact event equality on readback, including the
field, nullable strings and batch partitions. `transcode_exact`
also ties the native input and output to their own checked original
ranges through EOS. `transcode_late_error` preserves the ordered
completed prefix and original error in the refusal returned by the sink.

`emit_rechunk` compares two successful emissions at the same schema
whose input rows agree. `emit_scan_rechunk` carries that row equivalence
through logical filtering and positional projection, including width
zero. The exact trace for each emission retains its own partition.
The projected rows are observations of decoded events.

The event oracle pins genuine PyArrow input for both framing profiles
and their schema-only companions. It opens the resulting Lean streams
with PyArrow 26.0.1 and checks the descriptor, ordered nullable strings,
explicit empty batch, i64 UTF-8 offsets and exact modern EOS.

```sh
lake build --wfail Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Examples Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Axioms
python scripts/arrow-large-utf8/events_oracle.py /tmp/arrow-large-utf8-events
```
