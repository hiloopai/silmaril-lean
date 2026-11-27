# Checked plain Arrow Binary batches

`Silmaril.Formats.Arrow.Binary.Defs` provides `Binary.readColumn` for physical
buffers and `Binary.readBatch` for a caller-paired V5 Schema message, RecordBatch
message and record body. The IPC entry point admits one flat little-endian
Binary field (Schema.fbs tag 4) and retains its name and nullability. The caller
supplies the exact body and handles container framing and message pairing.
The profile excludes compression, dictionaries, nesting, and variadic buffers.

The record has one field node and three ordered, 8-byte-aligned buffer
descriptors for validity, offsets, and data. Every descriptor must fit within
the declared body. The decoder uses the existing per-message metadata, body,
row and field caps. The physical entry point caps the sum of the three buffer
lengths and requires correct cached byte lengths. An omitted validity bitmap
means all values are present. A supplied bitmap must cover every row, and the
exact observed null count must agree with the field node and field nullability.

Each logical offset is a nonnegative signed i32 read in little-endian order.
The initial word is required even for zero rows. Adjacent words must be
nondecreasing and within the data buffer, including for null slots. A nonzero
initial offset and unused trailing bytes are allowed. Typed offset errors
distinguish a missing word, a negative word, a descending next word, and a
word outside the data buffer. Present values are opaque byte slices. Equal
offsets at a present slot yield an empty byte sequence. A null bit yields
`none`.

`Binary.readBatch_sound` in `Silmaril.Formats.Arrow.Binary.Thms` records
the original metadata, exact checked body slices, and ordered slot relation.
`Binary.slot_octets` expresses a present slot as the exact octets of its
data interval.

The pinned fixture was written and independently reopened by little-endian
PyArrow 26.0.1. It contains a sliced array with opaque high bytes and embedded
zeros, a zero-row batch, an all-null batch, and a present empty byte sequence
with a zero-length data descriptor. The fixture SHA-256 is
`7568f3794bbecd9851fc57cbd058f17e7a2bf7a650aa1edaa13a23c9314fa410`.

```sh
python scripts/arrow-binary/batch_fixture.py
lake build --wfail Silmaril.Formats.Arrow.Binary.Examples Silmaril.Formats.Arrow.Binary.Axioms
```

## Opt-in IPC streams

Import `Silmaril.Formats.Arrow.Binary.Stream.Defs` for a complete V5 stream
over the same one-field profile. Choose `.modern` for the continuation word
and signed length, or `.legacy` for a single signed length word. The choice
applies to the entire carrier:

- Modern framing uses the eight-byte continuation prefix for messages and EOS.
- Legacy framing uses a four-byte prefix, padded metadata ending at an
  eight-byte body boundary, and a four-byte zero EOS.
- The first frame is a bodyless Schema. Every subsequent nonterminal frame is a
  RecordBatch under that same field declaration. Explicit EOS must exhaust the
  carrier. A cut-off marker is a framing error, and any byte after the marker
  is a trailing-bytes error.

`Stream.openInput` validates the schema and returns a cursor over the original
immutable carrier. `Cursor.next` returns one checked batch and its successor,
or a terminal reply. Failures after open retain their typed cause, zero-based
record ordinal and absolute prefix offset. `Stream.readAll` retains preceding
successful batches on failure. `Stream.read` returns a complete observation
after exact EOS. Both count empty RecordBatch messages against the stream batch
limit. Metadata, row and body caps are per message and the cursor retains the
whole input.

`Stream.read_sound` links the exact field and ordered batches to their original
frame ranges and the final EOS. `Stream.readAll_failed_prefix` links a failure
to the corresponding pull, with an ordinal equal to the number of preceding
batches. `Stream.next_suffix_error` gives the specific refusal at an EOS marker
followed by extra bytes.

The fixture script now independently writes and reopens both PyArrow 26.0.1
profiles, including schema-only companions. The legacy stream SHA-256 is
`aa065a17a00f75fed596fce07cbbd0018b623e7ceb02c955604a0d9aa539f125`.
The Lean tests check exact octets, descriptor and original ranges in both
profiles. Synthetic controls cover a late negative offset, short body, repeated
Schema, short EOS, and trailing data.

```sh
python scripts/arrow-binary/batch_fixture.py
lake build --wfail Silmaril.Formats.Arrow.Binary.Stream.Examples Silmaril.Formats.Arrow.Binary.Stream.Axioms
```

## Opt-in modern IPC stream writer

Import `Silmaril.Formats.Arrow.Binary.StreamWriter.Defs` for
`StreamWriter.emit limits field batches`. Use one field declaration and an
ordered list of batches, each a list of optional `KBytes`. The writer emits a
V5 plain Binary schema, record batches, and a modern continuation EOS. It
writes one validity, one signed-i32 offsets, and one data descriptor per
record. Offsets start at zero and repeat for null and empty values. A null
occupies a zero validity bit. Present bytes are opaque, including non-UTF-8.

Required fields admit present values only. The total data length of each batch
must be below `2^31`. Metadata, row and padded body limits apply per message,
and the batch limit applies to the stream. The writer builds the complete
carrier and checks it with the modern stream reader. Its success theorem
`StreamWriter.emit_readback` in the `Thms` module recovers the exact field and
ordered nullable octets by batch, together with the original frame ranges and
exact EOS. The batch list distinguishes a schema-only stream from one empty
RecordBatch.

The little-endian PyArrow 26.0.1 oracle independently opens the emitted streams,
validates plain Binary descriptors and values, and checks framing through EOS.
It covers nullable and required fields, nulls and present empty values,
schema-only output, and a single empty batch.

```sh
lake build --wfail Silmaril.Formats.Arrow.Binary.StreamWriter.Examples Silmaril.Formats.Arrow.Binary.StreamWriter.Axioms
python scripts/arrow-binary/stream_writer_oracle.py /tmp/arrow-binary-oracle
```

## Standard Arrow batch events

Import `Silmaril.Formats.Arrow.Binary.Stream.Events.Defs` for a standard
`Arrow.Events.BatchReader` over either framing profile. Its schema has one
`.binary` column labeled by the exact field name and nullability. A present
cell is an opaque `KBytes`. The adapter delegates each step to the native
cursor and converts the returned batch without changing the row count or
nullable slots. An empty RecordBatch still produces one event.

`Events.readAll` uses the configured batch limit plus one pull to check the
terminal marker or report the next indexed failure. An invalid Schema is an
open error. A later failure produces `.readError (.record failure)` with the
original ordinal, byte offset and cause, after the successful event prefix.
A caller-supplied shorter budget on the generic driver can produce `.closed`.
The cursor holds the whole source carrier. Successful frame ranges and the
EOS byte offset are available through the native trace used in the laws.

`Events.readAll_exact` proves equality of the standard driver trace and the
native cursor trace after converting batches and the terminal reply.
`Events.readAll_failure` links the event prefix to its original cursor steps
and first failing attempt. The pinned modern and legacy PyArrow fixtures
check the descriptor, opaque octets, explicit empty and schema-only cases,
and synthetic late offset and trailing-data failures.

```sh
python scripts/arrow-binary/batch_fixture.py
lake build --wfail Silmaril.Formats.Arrow.Binary.Stream.Events.Examples Silmaril.Formats.Arrow.Binary.Stream.Events.Axioms
```
