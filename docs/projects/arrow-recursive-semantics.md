# Physical semantics of a checked recursive Arrow IPC V5 batch

`Arrow.RecursiveSchema.Batch.Semantics.decode` consumes a
[checked RecordBatch layout](arrow-recursive-batch.md) for signed INT32,
signed INT64, Struct, and List. `readFirst` pairs the original recursive
schema with its first checked frame before beginning semantic validation.
The observation contains one physical column tree per field in declaration
order and retains the RecordBatch row count, including at width zero.

Each node has two independent bit arrays. The physical validity array
comes from the node's own bitmap and has exactly its declared null count.
An omitted bitmap represents all valid slots. The decoder visits exactly
the logical bits and ignores trailing bitmap padding. A slot is visible
when every ancestor is visible and valid at the corresponding position.
Struct children share their parent's physical index. Each List window
passes its parent's presence to all child slots between its two original
offsets. The windows are consecutive and disjoint, so propagation visits
each child slot once.
[Arrow Struct validity](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#struct-validity) ·
[Arrow List layout](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#list-layout)

A nonnullable declaration requires a valid bit wherever its slot is visible.
Physically null children under a null Struct or in a null List's window
remain admissible. Their bits still participate in the physical null
count. Primitive payloads retain all signed little-endian words, including
words at null or hidden slots. Those words have no logical value at an
absent slot. A present Struct with all-null children has its parent bit
set. A present empty List has its parent bit set and equal adjacent offsets.
A null List can have a nonempty physical window. The result exposes physical
columns and original windows. Row materialization and stream iteration
remain separate steps.

`decode_wire` and `readFirst_wire` bind the aligned observation to the
original schema, descriptor vectors, and absolute original buffer ranges.
The witness proves each logical bitmap bit, exact physical null counts,
and the signed fixed-width word partition. `PresenceWire.required_at`
gives the nonnullable rule on visible slots. `PayloadWire.list_endpoints`
and `PayloadWire.list_window` bind the original List words.
`listVisibility_window` and `PayloadWire.list_visibility_size` check
propagation and its exact child extent. The checked batch's slot budget
bounds the work in the physical tree.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-semantics-oracle/Axioms.lean
python3 scripts/arrow-recursive-semantics-oracle/check.py
```

Pinned PyArrow regenerates three genuine IPC streams. They include the
four-level predecessor with a populated and a sliced empty batch, a
positive row count at width zero, and hidden required nulls in a genuine
Struct child and a nonempty null List window. The oracle compares actual
raw bytes and signed words, the physical bit arrays and List windows, and
PyArrow's logical nested values. Seven labeled edits cover six typed
refusals and one padding control. Flipping only padding leaves the
observation unchanged. Exposing a hidden required null fails at its
original node and slot.
[Fixture pins](../../scripts/arrow-recursive-semantics-oracle/fixtures.json)
