# Native mixed Arrow IPC to ordered Parquet row groups

`Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.convert source sink input`
reads one immutable IPC V5 stream through the existing [mixed native
reader and typed observation][reader]. The compatible descriptor is
exactly one Int32 field followed by one BinaryView field. The Parquet
schema takes their exact names and required/optional flags in that
order. The sink requires distinct, nonempty names. BinaryView slots
become physical BYTE_ARRAY values by copying their opaque octets.
Nulls, present empty values, embedded zero and non-UTF-8 bytes remain
distinct.

The adapter completes native framing and exact EOS checks before
planning. Each record batch supplies the two typed lists for one
[mixed Parquet V1 row group][writer] at the same ordinal. Empty batches
become real zero-row groups with page headers. A schema-only input has
zero batches and returns `plan noBatches` under the sink's nonempty-plan
policy. A reversed schema returns `plan fieldOrder`. Other IPC kinds
remain subject to the checked reader's typed profile.

## Either field order and any admitted batch count

`MixedV1Writer.FromIpc.Complete.convert source sink input` reads the
native stream once through exact EOS. It sends the admitted observation
to the footer-only writer for zero batches and to the ordered row-group
writer for every other batch list. An explicit zero-row batch still has
its own group. The two physical Parquet leaves follow the IPC descriptor.
The ordered reverse API, `Int32ByteArrayGroup.ToIpc.convertOrdered`,
binds the two named leaves and derives their relative order from the
checked footer.

The [unified laws][combined] prove agreement with `SchemaOnly.convert`
on a checked empty batch list and `convertOrdered` on a checked
nonempty list, including exact sink refusals. Source admission failures
retain their original tag and indexed cause in all three paths.
`read_roundTrip` proves exact observation equality, including the ordered
descriptor, paired values and all empty batch positions, on successful
conversion and return. It uses a common group and footer policy for
certification and reopening. The reverse file and IPC caps remain
independent, including the returned carrier cap.

The [unified oracle][combined-oracle] pins both shapes in either order,
including zero batches, one empty batch and `[0, 2, 0, 1, 0]`. It checks
late body truncation and missing EOS before sink admission.

## Explicit page cuts

`MixedV1Writer.FromIpc.Complete.PageCuts.convert source limits policy input`
opts into the [multi-page Parquet writer][page-writer]. Its policy has one
entry per batch in source order. Each entry supplies an INT32 slot-count
list and a BYTE_ARRAY slot-count list, independent of physical field
order. Positive counts must sum to the batch length in each column. An
explicit zero-row batch takes `[0]` for each column. A schema-only stream
takes an empty policy and uses the same footer-only writer.

The converter admits the source through exact EOS before policy checks.
Aggregate and per-column page limits bound the plan, and the native
writer checks group, row, page and wire budgets before returning a
carrier. The [cut and readback laws][cut-laws] prove exact reconstruction
of both slot lists and of the ordered IPC observation through EOS, under
the declared writer and reverse reader policies. The [oracle][cut-oracle]
checks both field orders, uneven cuts, empty groups, wire caps and late
source refusals with pinned PyArrow and Thrift.

## Original INT32-first adapter

Source and sink limits are separate. The source applies the carrier,
framing, row/cell, and view bounds. The sink applies its own group,
aggregate row, file, footer, page, and scalar bounds, then its checked
mixed-reader limits. The adapter uses the checked source observation in
memory before constructing a complete file. It returns no file on a
source, planning or sink failure. Late truncation and missing EOS retain
their original native reader error and index.

[`prepare_exact`][laws] relates the labels and ordered pairs to the
source observation. `convert_indexed` relates each checked IPC batch to
the actual Parquet group's original wire chunks and exact ordered
nullable slots. `convert_schema_only` expresses the distinct no-batch
case. Source and sink error laws retain their stage and cause.

The [oracle][oracle] runs PyArrow 26.0.1 on eight pinned Arrow carriers
and compares the three genuine Lean files through PyArrow and Thrift
0.25.0. Success includes group shapes `[3, 0, 2]`, `[2, 1]`, and
`[0]`, nullable and required fields, and opaque binary inputs. The
oracle checks exact names, nullability, body bytes and indexed rows,
with ten typed refusal controls.

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Checks
python3.13 scripts/arrow-mixed-ipc-to-parquet-oracle/check.py --out /tmp/arrow-mixed-ipc-to-parquet
```

[reader]: arrow-mixed-named-table.md
[writer]: parquet-mixed-v1-multi-writer.md
[laws]: ../../Silmaril/Formats/Parquet/MixedV1Writer/FromIpc/Thms.lean
[oracle]: ../../scripts/arrow-mixed-ipc-to-parquet-oracle/check.py
[combined]: ../../Silmaril/Formats/Parquet/MixedV1Writer/FromIpc/Complete/Thms.lean
[combined-oracle]: ../../scripts/arrow-mixed-parquet-schema-only-oracle/check.py
[page-writer]: parquet-mixed-v1-multipage-writer.md
[cut-laws]: ../../Silmaril/Formats/Parquet/MixedV1Writer/FromIpc/Complete/PageCuts/Thms.lean
[cut-oracle]: ../../scripts/parquet-mixed-ipc-page-cuts-oracle/check.py
