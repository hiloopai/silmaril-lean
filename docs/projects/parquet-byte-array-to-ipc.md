# Write BinaryView IPC from one selected Parquet BYTE_ARRAY leaf

`Parquet.Plain.ByteArray.ToIpc.convert` takes immutable Parquet bytes,
one selected field name and required or optional layout, and separate
Parquet, IPC and view-column limits. It uses the checked file reader
for flat, uncompressed PLAIN BYTE_ARRAY Data Pages V1 and V2 in its
existing profile. The projection stays explicit even when the file
has other columns. The selected field becomes one BinaryView field
with its exact name and nullability. Present values remain opaque
octets. [Parquet reader profile](parquet-plain-byte-array-file.md) ·
[Arrow writer profile](arrow-binary-view.md)

The converter reads the entire selected column before emitting native
Arrow IPC V5. Each successfully exhausted footer group becomes one
ordered RecordBatch, including an admitted zero-row group. A source
with no footer groups produces a schema-only stream. Both streams
terminate with explicit EOS. `convert_readback` witnesses the original
indexed groups, the exact field, the batch and row counts, and the
nullable octets within each batch. It also gives their flattened table
observation. [Theorem header](../../Silmaril/Formats/Parquet/Plain/ByteArray/ToIpc/Thms.lean)

The pure result carries either complete stream bytes or the original
error tagged with its stage. Source admission and the first indexed
source read failure precede any writer error. The abstract Parquet
trace retains preceding complete groups even when a late source
failure prevents emission. The writer's original record index and
limit cause are available after successful source exhaustion.

## Independent checks

CPython 3.13.5, PyArrow 26.0.1, and Apache Thrift 0.25.0 check six
pinned Parquet inputs. PyArrow reads four actual Lean-emitted streams
and independently compares their V5 metadata, one-field schema,
footer-ordered batch sizes, nullable octets, and final EOS.

| Source | Expected batch sizes |
| --- | --- |
| Optional PLAIN V2 from column ordinal 1 | `[4, 4]` |
| Required PLAIN V1 | `[12, 12, 12]` |
| Schema-only Parquet | `[]` |
| Framed zero-row V2 group | `[0]` |

The zero-row group fixture uses an original in-file Data Page V2
header at byte 4. PyArrow independently reads that group. A separate
PyArrow-produced zero-row group with page offsets of zero is rejected
by the checked Parquet footer. The late source control changes the
length word at byte 162 and reports group 1, column 1, page 0, header
byte 136 with an unchanged first group. Writer controls cover a
12-byte value limit and an IPC batch-count limit.
[Fixture hashes](../../scripts/parquet-byte-array-to-ipc-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Checks +Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Checks
python3.13 -B scripts/parquet-byte-array-to-ipc-oracle/check.py --out /tmp/parquet-byte-array-to-ipc
```

[Parquet Format 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Arrow 26.0.1 BinaryView and IPC](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

## Typed hex CSV interchange

`Parquet.Plain.ByteArray.ToCsv.exportCsv` reads the actual BinaryView IPC
produced by the checked selected-column converter through exact EOS.
The caller supplies the selected leaf name and its required or optional
Parquet layout. The CSV result carries the exact name and nullability
with the BinaryView descriptor out of band. Its opaque cells use `N`
for null and `T` followed by uppercase hex for present bytes. A lone
`T` represents a present empty value.

`ToCsv.convert` also imports that checked CSV and returns the CSV and
final BinaryView IPC together. The intermediate stream keeps one batch
per footer group. CSV flattens the groups in footer order, and the final
stream emits one batch through exact EOS. Both a schema-only file and
an admitted zero-row group therefore yield a single zero-row final
batch. The final writer's per-batch row cap applies to the total rows;
the intermediate writer's cap applies to each group.

The success laws tie CSV decoding and native readback to the selected
slots from the original checked footer groups. Parquet admission and
indexed read errors precede intermediate writer errors. Intermediate
errors precede the CSV export, CSV import and final writer stages.
The late-source law retains the original error and the preceding groups
in the separate source trace. [Theorem header](../../Silmaril/Formats/Parquet/Plain/ByteArray/ToCsv/Thms.lean)

PyArrow independently reads the selected column from the four fixtures
above and compares it with both actual BinaryView stages. CPython checks
the CSV tokens and generates separate CSV inputs that Lean imports.
[Comparator](../../scripts/parquet-opaque-typed-csv-oracle/check.py) ·
[Artifact pins](../../scripts/parquet-opaque-typed-csv-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Checks
python3.13 -B scripts/parquet-opaque-typed-csv-oracle/check.py --out /tmp/parquet-opaque-typed-csv
```

### Typed hex CSV back to Parquet

`Parquet.Plain.ByteArray.FromCsv.convert` accepts the out-of-band
BinaryView descriptor and checked typed hex CSV. The descriptor
supplies the exact leaf name and required or optional layout. Bounded
CSV decoding validates the header, tags, hex, byte and row limits
before the unannotated PLAIN V1 BYTE_ARRAY writer runs. Each successful
file has one leaf at column zero and one framed row group at group zero,
including for header-only CSV.

`convert_readback` ties the exact checked footer and group zero to the
CSV's original ordered slots. A present empty value and a null slot
remain distinct. The error laws preserve the typed CSV refusal before
any writer check, and the original writer error after CSV admission.

`roundtrip` composes the original checked Parquet export and native
import under their respective limits. The returned group contains the
original selected slots flattened in footer order. The comparison is
on the descriptor and rows. The output writer always uses one group.
[Reverse bridge laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/FromCsv/Thms.lean)

The comparator reuses the four pinned forward sources and reads the
actual Lean CSV from each. PyArrow and CPython with Thrift verify five
Lean-produced files, including a standalone required header-only CSV,
and compare names, nullability, ordered octets, and native page framing.
[Comparator](../../scripts/parquet-byte-array-from-typed-csv-oracle/check.py) ·
[Artifact pins](../../scripts/parquet-byte-array-from-typed-csv-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv.Checks
python3.13 -B scripts/parquet-byte-array-from-typed-csv-oracle/check.py --out /tmp/parquet-from-typed-csv
```
