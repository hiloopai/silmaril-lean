# Selected flat Parquet columns

`FlatColumn.bindColumn snapshot selection` binds an exact name, physical
type and required or optional layout against a `Snapshot.Checked`. The
result type is `Binding snapshot selection`. The binding carries the matched
footer leaf and its zero-based column ordinal. Its serialized schema ordinal
is one greater because the root occupies entry zero. Binding requires direct
physical leaves under the root and uses the footer's distinct-name check.
Column path, physical type, and value count are checked again before using
the selected chunk's offsets.

`FlatColumn.readColumn binding limits policy decode groupIndex` takes a
zero-based group index and returns ordered nullable slots. The callback is

```lean
Footer.SchemaElement → Footer.ColumnMetadata → Page.Header → Bytes →
  Except ε (List (Option α))
```

The header and complete on-disk body are from the same checked frame and
snapshot. Callbacks can use `FlatColumn.pageParameters` with the matched
layout and column codec. This preserves the original header sizes, counts,
and resolved V2 compression flag. The traversal checks the number of slots
per page, required presence, and the declared V2 null count. Encoding-specific
interpretation, byte consumption, and decoder workspace bounds are callback
responsibilities. [Binder and callback][defs] · [Snapshot](parquet-snapshot.md)

## Admission

- Codec 0 and one configured value encoding. The footer must advertise that
  encoding and may also advertise RLE (3) for levels. The actual encoding is
  checked for every data page.
- V1 with RLE definition and repetition level tags, and V2 with no repetition
  section. The caller can select V2-only. Required V2 pages must declare no
  definition bytes or nulls. V2 row and value counts must agree.
- CRC-bearing frames, dictionary pages, non-data pages, dictionary and index
  page offsets, and external column paths are rejected. The footer parser
  accepts an absent or empty external path. OffsetIndex, ColumnIndex and
  Bloom metadata play no role in the read. There is no logical annotation
  interpretation.
- The selected chunk is bounded before framing. Both declared page byte
  sizes and the group and page slot limits are checked before extracting
  bodies. The declared page counts must sum to the group row count. Errors
  carry group and column ordinals and the column name. Page admission and
  callback errors also carry the page ordinal and absolute header offset.
  An unsuccessful chunk framing returns the underlying typed `Page.Error`
  at the group and column. Within each column framing and admission precede
  body decoding.

`FlatColumn.readColumnFor .snappy` opts into codec 1 and verifies any
page CRC over the complete stored body before the callback.
`readColumnFor_checked_wire` pairs that checksum result with each
original frame and callback result. The Snappy STRING decoder uses
this path. [Snappy STRING profile](parquet-utf8-view.md#opt-in-snappy-plain-string)

## Mixed BOOLEAN and FLOAT profile

`MixedBooleanFloat.openFile` checks the file byte cap and binds exactly two
named optional leaves in file order. BOOLEAN uses RLE (3) and FLOAT uses
BYTE_STREAM_SPLIT (9). FLOAT slots are raw `UInt32` words, including NaN
payloads and signed zero. `Checked.readGroup` returns ordered typed rows.
`MixedBooleanFloat.readAll` publishes complete batches through the Snapshot
event reader in group order. It stops at the first failing group, and inside
a group it reads BOOLEAN before FLOAT. Existing single-column readers and
the default FlatScan profiles have their own entry points.
[BOOLEAN byte and slot laws](parquet-rle-boolean-page.md) ·
[FLOAT byte and slot laws](parquet-byte-stream-split-page.md)

`FlatColumn.binding_leaf` identifies the serialized schema entry and its
name, physical type and layout. `FlatColumn.readColumn_wire` witnesses the
group and chunk lookups, original `Page.readChunk` equation, exact body
callback results in frame order, and both declared and returned counts.
`MixedBooleanFloat.openFile_snapshot` identifies the checked source.
`MixedBooleanFloat.readGroup_wire` relates both ordered slot streams to that
group and gives the exact row at each position. Assembly indexes two arrays
of the same proved length. Changing page boundaries while keeping the two
flattened slot streams leaves the assembled rows identical.
[Column theorems][column-thms] · [Mixed theorems][mixed-thms] ·
[Frame geometry](parquet-page-framing.md)

## Independent files

Parquet Format **2.14.0** is pinned to
`04d56f291ff963e98bc37ab8100e2fc133ff583c` with `parquet.thrift` SHA-256
`d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
The oracle uses PyArrow **26.0.1** from
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` and Apache Thrift **v0.25.0** from
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. Thrift checks the actual page
tags and exact page extents. Each clean file contains three groups of 16
rows. In every group the BOOLEAN page counts are `[4, 4, 4, 4]` and the FLOAT
page counts are `[12, 4]`. PyArrow and Lean check all nullable slots and
FLOAT words. [Pins and fixture provenance](arrow-parquet-coverage.md) ·
[Producer package pins](parquet-flat-page.md#independent-page-fixtures) ·
[Oracle][oracle]

| Fixture | SHA-256 |
| --- | --- |
| `mixed-boolean-float-v1.parquet` | `20b5cb8af03a0eb748ee5544d7ab55f30d9d2ef660b050f62922caf3bcea67cc` |
| `mixed-boolean-float-v2.parquet` | `e50068d293b553d9130ae8758b86306f498b5084fe8485f896b1251dd57d5bf6` |
| `mixed-boolean-float-v2-bad-length.parquet` | `f2379879ddb72255943b8801c806f758b0e9180af2f096d921809053f87a6a16` |

The damaged file raises the Boolean value length at byte 291 from two to
three. PyArrow reads groups 0 and 2 and rejects group 1. Lean emits the
complete 16-row group 0 and stops with `lengthMismatch` at group 1,
column 0 (`enabled`), page 1, header byte 265. The regressions also exercise
schema binding, a V2-only policy, page bounds, wrong callback output
and null counts, and a FLOAT header tag change after the BOOLEAN
column has succeeded. [Lean regressions][tests]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-mixed-boolean-float/Oracle.py "$fixture_tmp"
diff -r data/parquet-mixed-boolean-float "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.MixedBooleanFloat.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.MixedBooleanFloat.Tests +Silmaril.Formats.Parquet.RleBoolean.Tests +Silmaril.Formats.Parquet.FloatByteStreamSplit.Tests parquet-footer-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-mixed-boolean-float/Axioms.lean
```

[defs]: ../../Silmaril/Formats/Parquet/FlatColumn/Defs.lean
[column-thms]: ../../Silmaril/Formats/Parquet/FlatColumn/Thms.lean
[mixed-thms]: ../../Silmaril/Formats/Parquet/MixedBooleanFloat/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/MixedBooleanFloat/Tests.lean
[oracle]: ../../scripts/parquet-mixed-boolean-float/Oracle.py
