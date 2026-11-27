# Ordered mixed Arrow TIMESTAMP and typed CSV

`Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp` connects the native
`Arrow.MixedFlat.Timestamp` stream and the packed named-table API to typed
UTF-8 CSV. The caller supplies the ordered field declaration, including each
name, INT32/UTF8/TIMESTAMP kind and requiredness, and each timestamp's unit and
absent or exact `UTC` timezone. The CSV header checks names in position. Types,
requiredness and timestamp descriptors stay in the declaration. The CSV wire
carries exact signed decimal tick counts in the declared units, with no unit
conversion or time-zone interpretation.

The shared typed UTF-8 CSV codec uses `N` for null and `T` followed by text
for a present value. Thus `T` is present empty text, and `TN` is present
literal `N`. Quoting follows the existing RFC 4180 UTF-8 profile, including
escaped double quotes and embedded CRLF and commas. The profile rejects
unrepresentable control bytes such as NUL. Width zero uses the existing quoted
empty record marker for the header and each row. Position distinguishes repeated
field names when the downstream format admits them.

CSV flattens the ordered logical rows. Empty source batches contribute no rows.
Import writes one new batch, including a zero-row batch for a header-only file.
`RowEquivalent` requires exact field declaration equality and exact equality
of the aligned dependent rows. `ipc_roundtrip` proves this equivalence for
successful conversion in both directions. `ipc_parquet_roundtrip` transfers
it to the existing mixed PLAIN V1 Parquet writer and ordered Events reader when
that writer also admits the re-emitted IPC. Its positive-width, distinct valid
name and modern timestamp unit constraints still apply. The resulting Parquet
group corresponds to the newly emitted batch.

IPC export checks the original stream through exact EOS before CSV admission.
CSV input checks byte limits, the declaration and the header before body rows.
Rows are visited in order. A nonempty suffix at the row limit returns the limit
error. Otherwise, lexical validation, width, and left-to-right tagged decoding
precede the first required-null check for that row. A row failure prevents
advancing to the next row or starting IPC output. Body row and column coordinates
are zero-based and count logical records, including quoted line breaks inside
one record. Named insertion follows the shared policy of name occupancy, complete
decoding, and exact schema equality. Successful insertion updates only the
specified name.

## Reproduce

```sh
lake build --wfail Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-mixed-timestamp-csv-oracle/Axioms.lean
python3 scripts/arrow-mixed-timestamp-csv-oracle/check.py
```

The [SHA-256 pins](../../scripts/arrow-mixed-timestamp-csv-oracle/fixtures.json)
cover three independent CPython 3.13.5 CSV files, four genuine PyArrow 26.0.1
IPC streams, and a labeled trailing-byte mutation. Python's standard CSV
reader checks actual Lean CSV, and PyArrow checks actual Lean IPC and Parquet
outputs positionally. The comparator includes all three modern units, UTC
and local timestamps, signed endpoints, Unicode, literal tags, null and empty
text, embedded CRLF and quoting, reordered declarations, zero-width row counts
and header-only input.
