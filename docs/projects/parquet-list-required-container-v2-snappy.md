# Snappy PLAIN V2 for a required Parquet LIST

`ListFile.RequiredContainer.V2.Snappy.convert` admits the canonical
required LIST of nullable signed INT32 in a local Snappy column. Each
group uses one complete PLAIN V2 frame. The checked footer binds
the original LIST annotation, repetition flags, path, codec and
group ordinal. The existing V1, uncompressed V2 and optional-container
entry points keep their own admission conditions.
[Required-container V2](parquet-list-required-container-v2.md) · [Optional-container Snappy V2](parquet-list-snappy-v2.md)

## Original body and counts

The original immutable source supplies the whole stored frame to the
checksum verifier. A present signed Thrift CRC is compared as its raw
32 bits against the stored repetition, definition and value bytes. An
absent checksum is a separate admitted status. The body is checked before
level decoding or expansion. File input, stored body, expanded page and
both raw level sections have explicit bounds.
[Stored CRC wire contract](parquet-page-crc32.md)

The two level lengths select their original raw spans. The resolved
`is_compressed` flag selects one exact Snappy member when true and the
unchanged suffix bytes when false. An omitted flag has the standard
default of true. The expanded suffix is exactly four bytes per physical
value slot. The Parquet level law identifies `num_values` with the
original slots, `num_rows` with repetition-zero starts, and
`num_nulls` with empty-list markers and null child slots. Rows start
at a page boundary and the page totals agree with the selected group.
The required parent stays present, including when the list is empty.
[Pinned V2 header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L788)

The native readback preserves the required LIST descriptor, nullable
children, signed word order, group order and exact EOS. Page-body errors
carry the original group, frame ordinal and header offset. Framing
errors retain their original typed cause and group. The first source
failure retains earlier batches and takes precedence over writer refusal.

## Independent fixtures

PyArrow 26.0.1 writes two native files, with and without CRCs. Each has
one raw suffix and one Snappy suffix in separate groups. Thrift checks
the original header, raw spans, suffix extents and three page counts.
Zlib independently checks both stored CRCs. PyArrow verifies the
Parquet input and Lean's V5 IPC output, including the original field
nullability, nullable rows and signed endpoints.

The labeled assembled flag control uses the default compressed flag.
Mutations cover stored CRC failures in a raw suffix, a raw level span and
a Snappy suffix. A separate invalid Snappy suffix with a valid computed
CRC exercises the decompressor. Count and flag controls preserve the
preceding group and run under a zero IPC row cap.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Hashes and observations](../../scripts/parquet-list-required-container-v2-snappy/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-required-container-v2-snappy/Oracle.py "$replay" |
  diff -u scripts/parquet-list-required-container-v2-snappy/observations.txt -
```
