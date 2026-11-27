# Arrow IPC streams through a named table to UTF-8 CSV

`Silmaril.Formats.Arrow.ToCsv.Utf8.convert` uses the existing checked Arrow
IPC byte reader, ordered schema translation, and EOS-only named insertion.
It exports the table with `Csv.NamedTable.Utf8.exportCsv` and returns the
updated database, ordered schema, and CSV bytes together on success. The
caller supplies the expected schema and observation limits. Other named
entries are preserved by the existing packed update. A malformed stream or
an unrepresentable CSV field returns an error without a database result.
[IPC reader contract](arrow-ipc-stream.md) · [Typed UTF-8 CSV](typed-utf8-csv.md) ·
[Named UTF-8 CSV](named-utf8-csv.md)

The reader profile is a finite little-endian flat Arrow IPC V5 stream with
Int32 and UTF-8 fields and modern EOS. Multiple batches flatten in input
order, including empty batches. Field names keep their exact UTF-8 bytes;
position, kind, and nullability remain in the returned schema. Null and
present empty text have distinct typed CSV tags. The UTF-8 wire profile
still rejects disallowed ASCII control bytes, including tab and NUL.

`ToCsv.Utf8.convert_roundTrip` proves the exact named update and recovery of
flattened ordered Arrow rows when the checked source table can be encoded.
`convert_byteError` and `convert_encodeError` preserve those failure reasons.
`FromCsv.Stream.emitCsvUtf8_readback` composes the existing CSV adapter with
the stream writer's checked-reader law. Successful emission recovers the
exact declared fields and nullable cells in order under the same limits,
plus the explicit record-batch row count even when there are no columns.
The reverse bridge emits the decoded table in one batch.
[Forward theorems](../../Silmaril/Formats/Arrow/ToCsv/Utf8/Thms.lean) ·
[Reverse theorems](../../Silmaril/Formats/Arrow/FromCsv/Stream/Thms.lean)

The scoped examples check a multi-batch stream, late truncation, trailing
bytes, schema and name conflicts, a CSV wire encoding error, and a positive
row count at zero columns. The independent oracle reads the existing pinned
PyArrow fixture with batch sizes `[4, 0, 1, 1]`, generates canonical UTF-8
CSV with CPython's `csv.writer`, and compares exact bytes. PyArrow also reads
the re-emitted IPC and checks all six rows in order.
[Fixture provenance](../../tests/formats/arrow-ipc/fixture.json)

```sh
lake build --wfail +Silmaril.Formats.Arrow.ToCsv.Utf8.Examples +Silmaril.Formats.Arrow.FromCsv.Stream.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.ToCsv.Utf8.Examples +Silmaril.Formats.Arrow.FromCsv.Stream.Examples'
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/arrow-to-csv-utf8-oracle/Read.lean tests/formats/arrow-ipc/nullable-int32-utf8.arrows /tmp/utf8.csv /tmp/utf8.arrows
python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
python3 -I scripts/arrow-to-csv-utf8-oracle/verify.py /tmp/utf8.csv /tmp/utf8.arrows
```

## Direct ordered mixed IPC and Scan

`Csv.Typed.Utf8.MixedIpc.convert` reads the complete native mixed IPC
stream through its Scan materializer, then exports the ordered table.
The admitted fields are INT32, UTF8, and Utf8View. The result carries
the full Arrow descriptors alongside the UTF-8 CSV bytes. The CSV
header contains names in position order, including duplicates.
Re-import takes the descriptor separately and checks the exact header,
cell kinds, required cells, row bound, and input byte bound.

Positive-width fields use `N` for null and `T` followed by the present
UTF-8 text or canonical signed decimal. The typed CSV profile represents
a zero-column header and each zero-column row with a single empty
field. A positive-width table with no rows emits the header alone.
The output byte cap applies after encoding. BinaryView and other field
kinds outside the profile receive an indexed schema error. The existing
UTF-8 wire alphabet governs representability.

`convert_roundtrip` returns the exact Scan observation after checked
re-import with the same CSV limits and descriptor. IPC batch boundaries
are flattened in source order by Scan materialization. The independent
oracle uses PyArrow 26.0.1 and CPython 3.13 to compare three IPC/CSV
round trips, including duplicate names, an empty middle batch, schema-only
input, and zero-width rows.
[Direct bridge laws](../../Silmaril/Formats/Csv/Typed/Utf8/MixedIpc/Thms.lean) ·
[Comparator](../../scripts/arrow-mixed-scan-csv-oracle/check.py)

### Checked single-batch native export

`Csv.Typed.Utf8.MixedIpc.ToIpc.convert` takes the explicit ordered Arrow
descriptor and bounded typed CSV. It finishes source import before
invoking the opt-in mixed IPC V5 writer for INT32, UTF8, and Utf8View.
The writer applies its own admission limits. Each successful output
has one RecordBatch and exact EOS. Header-only input emits a zero-row
batch, and a positive-row zero-width table retains its row count.

`convert_readback` recovers the exact dependent Scan table, including
all field descriptors, nullability flags, repeated names, and ordered
nullable cells. `encoded_readback` applies the same law to a table
exported by the typed CSV encoder when native output succeeds. The
independent comparator reads the four actual Lean streams in PyArrow,
including both header-only forms and positive-row zero width.
[Reverse bridge laws](../../Silmaril/Formats/Csv/Typed/Utf8/MixedIpc/ToIpc/Thms.lean) ·
[Comparator](../../scripts/typed-csv-to-mixed-ipc-oracle/check.py)

### Native IPC round trip through typed CSV

When both checked conversions succeed, `MixedIpc.RoundTrip.readback`
recovers the original ordered descriptor and dependent Scan rows in one
output batch through exact EOS. The input reader, CSV export, CSV import,
and IPC writer each apply their supplied limits. `RoundTrip.equivalent`
compares the materialized rows and descriptor independently of batch
partition.

The pinned PyArrow input has batch sizes `[2, 0, 2]`. CPython compares
the exported CSV to the input rows, and PyArrow checks the actual Lean
output has the same descriptors and cells in a single four-row batch.
[Round-trip laws](../../Silmaril/Formats/Csv/Typed/Utf8/MixedIpc/RoundTrip/Thms.lean) ·
[Comparator](../../scripts/mixed-ipc-csv-row-roundtrip-oracle/check.py)

### Named tables with mixed IPC descriptors

`MixedIpc.NamedTable.importCsv` decodes bounded CSV under its declared
descriptor, then uses the packed database's vacant-name and exact-schema
gate. The descriptor retains every field's position, kind, name and
nullability, including repeated names. `exportCsv` looks up the requested
name and checks the expected descriptor before encoding. It distinguishes
a missing entry, a descriptor mismatch and a typed encoding failure.

`import_exportCsv` copies the observed table into a vacant destination
at the same CSV limits and updates only that key. `ipc_roundtrip` relates
the original checked IPC rows, the inserted table and the checked IPC
returned after named export. Each stage has its own limits. The output
has one batch through EOS, including a zero-row batch for a schema-only
source. Positive-row zero-width tables keep their row count.
[Named bridge laws](../../Silmaril/Formats/Csv/Typed/Utf8/MixedIpc/NamedTable/Thms.lean) ·
[PyArrow and CPython comparator](../../scripts/typed-mixed-csv-named-table-oracle/check.py)
