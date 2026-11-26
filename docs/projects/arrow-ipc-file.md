# Arrow IPC V5 file reader

The file reader covers the same flat little-endian nullable and required
Int32 and UTF-8 fields as the stream profile. It reads a finite immutable
`KBytes` source and provides indexed batches and ordered row observations.
The format pins are Arrow Columnar 1.5 and IPC metadata V5 at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and FlatBuffers at
`03fffb25e2d777462b719cb4964249c30b19d58f`.
[Coverage matrix](arrow-parquet-coverage.md) · [Stream profile](arrow-ipc-stream.md) ·
[File format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-file-format) ·
[File.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/File.fbs) ·
[FlatBuffers internals](https://github.com/google/flatbuffers/blob/03fffb25e2d777462b719cb4964249c30b19d58f/docs/source/internals.md)

## Footer and index

`FileFooter` retains the schema and ordered `FileBlock` entries after checking
V5, absent or empty dictionary and custom metadata vectors, and the supported
schema profile. Each inline block is 24 bytes with a signed 64-bit absolute
offset, a signed 32-bit metadata length including the continuation prefix
and metadata padding, and a signed 64-bit body length. The decoder rejects
negative values. The shared vector decoder checks element alignment for
nonempty vectors and checks the length word and extent for every vector.
[Metadata decoder and AST](../../Silmaril/Formats/Arrow/Metadata/Defs.lean)

`readFooterSpan` checks both `ARROW1` words, zero leading padding, the
signed little-endian footer length, its alignment and its extent against
the actual source. `readIndex` checks that the embedded schema matches the
footer schema exactly. The supported profile requires contiguous blocks in
physical order followed by the eight-byte modern EOS immediately before
the footer. Each block must be aligned, start at the current cursor, and
end before the footer. This checks the full index before any indexed
metadata or bodies are sliced.
[File reader definitions](../../Silmaril/Formats/Arrow/FileReader/Defs.lean)

An indexed read checks the prefix and Message lengths against the selected
block, validates the record layout, and uses the existing body decoder.
An out-of-range index returns `none`. Indexed row reads check the selected
batch budgets. Full materialization checks aggregate rows and cells before
allocating row observations. Malformed input, unsupported features, and
configured limits use the same error classes as the stream reader.

## Laws and independent fixtures

`readFooterSpan_verified` and `FooterSpan.bytes_exact` characterize the checked
footer. `Index.block_range` and `Index.block_order` prove its range and
nonoverlap properties. `Index.readBlock_exact` proves that a successful
indexed read recovers the declared metadata and exact body octets.
`readRows_indexed` proves that materialization and indexed reads agree,
including batch order, empty batches, and out-of-range lookups.
[Theorem header](../../Silmaril/Formats/Arrow/FileReader/Thms.lean)

The pinned PyArrow 26.0.1 producer uses `pa.ipc.new_file`. Its independent
`pa.ipc.open_file` readback checks schema, batch lengths and ordered rows.
The fixtures include mixed nulls and multiple batches, an empty batch,
a schema-only file, and positive-row zero-column data. Dictionary and Int64
files are pinned rejection cases. Native Lean tests both indexing and
materialization and mutates footer lengths, offsets, schemas and block
extents.
[Fixture hashes](../../tests/formats/arrow-ipc/file-fixtures.json) ·
[Producer and wheel hash](../../tests/formats/arrow-ipc/fixture.json) ·
[Hash-pinned requirements](../../tests/formats/arrow-ipc/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Arrow.FileReader.Thms arrow_ipc_metadata_tests
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.FileReader.Thms arrow_ipc_metadata_tests'
python3 -I tests/formats/arrow-ipc/file_fixture.py --regenerate
```

Regeneration uses the environment installed from the hash-pinned requirements.
The scope is read-only. Dictionaries, nested types, compression, legacy
framing, and incremental file I/O remain outside the profile.
