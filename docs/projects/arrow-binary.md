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
