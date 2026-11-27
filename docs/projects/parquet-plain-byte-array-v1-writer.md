# Bounded PLAIN BYTE_ARRAY V1 page writer

`Silmaril.Formats.Parquet.PlainByteArrayV1Writer.emit limits input`
writes a checked, flat, uncompressed BYTE_ARRAY data page with a
Compact V1 header. Required input supplies a list of raw byte strings.
Optional input supplies a list of nullable byte strings. The writer uses
the [bounded PLAIN BYTE_ARRAY codec][plain] for the present values in
order. A present empty value has a four-octet zero length word. A null
contributes only to the definition mask. Embedded zero and non-UTF-8
octets remain unchanged.

A required page contains just the scalar bytes. An optional page starts
with a four-octet little-endian definition length and a width-one
singleton Hybrid RLE run for each slot. Empty required and optional
pages therefore have different body extents. The writer checks row,
definition and body caps before encoding the body, then applies the
existing Compact-header and scalar bounds. It reuses the INT32 writer's
header serializer and output type and checks the exact parsed header
and stop offset. The profile covers PLAIN encoding and codec 0, without
CRC, statistics, repetition levels, dictionary, V2, or a file envelope.

[`emit_exact`][laws] gives the checked header, both body sizes, total
wire extent and the exact scalar encoder outcome. `emit_prepared` gives
the original mask and scalar slice. `emit_roundTrip` proves that
`ScalarPage.decode` recovers the original ordered nullable slots under
the same limits. The writer checks the header at runtime. Body
readback follows from the proof.

The public format sources are Parquet Format 2.14.0 at
`04d56f291ff963e98bc37ab8100e2fc133ff583c` and Apache Thrift 0.25.0
at `27e8a425ffb498e190df3a12e239326bf5ba9ed6`. [Parquet encodings][encoding] ·
[PageHeader IDL][idl] · [Compact protocol][compact]

The [oracle][oracle] pins five Lean-emitted pages and three files built
by replacing a PyArrow-generated file's page and updating its footer
sizes using Thrift. Thrift 0.25.0 independently checks each Compact
header and an octet comparison checks the full body. PyArrow 26.0.1
reads the required, nullable mixed, and all-null files with the actual
Lean page bytes. The two zero-row cases remain standalone pages.
Lean exercises exact configured limits and seven refusal controls.

```sh
lake build --wfail +Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Checks
python3.13 scripts/parquet-plain-byte-array-v1-writer/check.py --out /tmp/parquet-byte-array-v1
```

## One-leaf native file

`PlainByteArrayV1Writer.File.emit` writes one named unannotated
BYTE_ARRAY leaf, one row group and one uncompressed PLAIN V1 page.
The page input determines the required or optional layout. Both layouts
admit zero rows and keep one explicit framed group. Optional cells
distinguish a null slot from a present zero-length byte string.

The writer measures the page and bounds the Compact footer before
allocating the page body. It uses the existing selected-column reader
with the supplied file, footer, chunk, page, row and value limits.
Publication requires the exact singleton footer and exact slots from
group zero at column ordinal zero.

`emit_wire` ties the native file to the bounded page at byte four, the
serialized Compact footer and the exact trailer. `emit_readback`
gives the checked footer and indexed group witness with the original
ordered slots. The error laws preserve assembly and indexed readback
causes. [File writer laws](../../Silmaril/Formats/Parquet/PlainByteArrayV1Writer/File/Thms.lean)

PyArrow 26.0.1 reads four complete Lean-emitted files, including empty
required and optional groups. CPython with Thrift 0.25.0 independently
checks the physical leaf, data offset, chunk sizes, complete V1 header
and exact level and scalar bytes. The fixtures include an embedded zero,
non-UTF-8 bytes and a value with all 256 octets.
[Comparator](../../scripts/parquet-plain-byte-array-file-writer-oracle/check.py) ·
[File pins](../../scripts/parquet-plain-byte-array-file-writer-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Checks
python3.13 -B scripts/parquet-plain-byte-array-file-writer-oracle/check.py --out /tmp/parquet-byte-array-file
```

[plain]: ../../Silmaril/Formats/Parquet/Plain/ByteArray/Thms.lean
[laws]: ../../Silmaril/Formats/Parquet/PlainByteArrayV1Writer/Thms.lean
[encoding]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[compact]: https://github.com/apache/thrift/blob/27e8a425ffb498e190df3a12e239326bf5ba9ed6/doc/specs/thrift-compact-protocol.md
[oracle]: ../../scripts/parquet-plain-byte-array-v1-writer/check.py
