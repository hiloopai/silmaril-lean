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
