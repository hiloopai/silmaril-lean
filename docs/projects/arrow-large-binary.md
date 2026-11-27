# Checked Arrow LargeBinary streams

`Silmaril.Formats.Arrow.LargeBinary.Stream.Defs` admits one flat,
little-endian Arrow IPC V5 LargeBinary field (Schema.fbs tag 19) and preserves
the field name and nullability. Call `LargeBinary.Stream.read` with either
`.modern` or `.legacy` framing. The choice applies from the bodyless Schema
through explicit EOS. Modern EOS is eight bytes and legacy EOS is four.
Truncation, a mixed framing profile, and bytes after EOS are refused.

Each RecordBatch has one node and three ordered descriptors for validity,
signed little-endian i64 offsets, and data. The descriptors must be aligned
and fit inside the original body. Offset zero is required even for zero rows.
Adjacent words must be nonnegative, nondecreasing and within the declared
data descriptor, including under null slots. Nonzero initial offsets and
unused trailing data are allowed. The data is opaque. A present zero-length
interval and a null slot produce distinct observations.

An empty RecordBatch preserves its position in the result and consumes one
batch budget unit. Schema-only input has no batches. Metadata bytes, body bytes
and rows are bounded per message. The batch budget applies to the stream.
Failures after Schema admission carry a zero-based ordinal, an absolute
frame offset and the nested cause. The reader materializes a complete ordered
observation on success.

`LargeBinary.Stream.read_sound` links the original schema, ordered record
ranges and exact EOS. `record_octets` gives the original bytes in each
metadata and body window. `LargeBinary.slot_octets` identifies the exact
opaque data slice for a valid slot. The shared offset decoder also serves the
existing plain Binary reader, whose tag 4 and i32 offsets retain their profile.

The fixtures were written and reopened with little-endian PyArrow 26.0.1 in
both framing modes. They include sliced input with invalid UTF-8 data, nulls,
a present empty value, a zero-row batch and a schema-only control. Separately
labeled synthetic mutations test a negative i64, descending offsets under
a null slot, and a final offset beyond the descriptor into body padding.

- Modern SHA-256 `34e14f731d9d5b060f36bda5531279050f93455805f49efda76a176744bad000`
- Legacy SHA-256 `c644bcc306aa2f743ee070ec12eed479075157bfd407480021da9c97c6955a78`

```sh
python scripts/arrow-large-binary/stream_fixture.py
lake build --wfail Silmaril.Formats.Arrow.LargeBinary.Stream.Examples Silmaril.Formats.Arrow.LargeBinary.Stream.Axioms
```
