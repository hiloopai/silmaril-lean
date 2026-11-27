# Ordered Hive manifest to native mixed Arrow IPC

`Hive.Manifest.Heterogeneous.ToIpc.convert` accepts the same supplied ordered
manifest of literal path and Parquet bytes as the checked heterogeneous Events
adapter. The declared schema determines the ordered physical INT32, UTF8 and
modern TIMESTAMP fields, followed by the typed INT32 and UTF8 virtual partition
fields. The adapter reuses the existing Hive binding and selected Parquet
readers. The IPC writer preserves the exact field names, positions, nullability,
and TIMESTAMP units and UTC/local descriptors.

Each reached Parquet group supplies one native IPC RecordBatch in file and
group order. Repeated paths are independent occurrences. Explicit zero-row
groups carry a zero-row batch, and an empty manifest emits its declared Schema
and EOS with zero batches. `convertProjected` applies the existing logical
Events projection, including reorder, repeated positions and width zero.
Width-zero IPC preserves every explicit row count through the same checked
writer and reader. The projection reads the full declared physical source and
retains failures from any of those fields.

Source validation runs through EOS before writer admission. A source schema or
reached file failure returns the original typed cause, including manifest
occurrence, path and any Parquet group/column coordinates. This holds under
output limits that would reject a valid source. A failure yields no IPC bytes.
The Events APIs retain the earlier complete batches for callers that need them.

`convert_readback` and `convertProjected_readback` connect successful bytes
to the ordered source observation and exact native IPC schema and EOS.
`convert_file_batches` connects the readback to each checked file with its
bound virtual constants in manifest order. The first-error laws keep the
original source cause across both full and projected export.

## Reproduce

```sh
lake build --wfail Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/hive-heterogeneous-ipc-oracle/Axioms.lean
python3 scripts/hive-heterogeneous-ipc-oracle/check.py
```

The [SHA-256 pins](../../scripts/hive-heterogeneous-ipc-oracle/fixtures.json)
cover three genuine PyArrow 26.0.1 Parquet files, the labeled late dictionary
mutation, and a separately labeled assembly using the existing explicit empty
V2 group control. The genuine paths cover escaped Unicode, an explicit null
partition, and an omitted optional partition key. PyArrow independently reads
the literal paths and source groups, then compares six actual Lean IPC streams
positionally through EOS, including duplicate manifest and field positions.
The comparator runs with CPython 3.13.5 and Thrift 0.25.0.
