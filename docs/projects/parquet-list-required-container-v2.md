# Uncompressed V2 required Parquet LIST

`ListFile.RequiredContainer.V2.convert` admits the same canonical required
LIST of nullable INT32 as the existing V1 reader. Each row group uses one
complete local PLAIN Data Page V2 frame. Admission requires codec
UNCOMPRESSED and an absent stored CRC. Both resolved suffix flags select
raw bytes under codec zero, with equal advertised stored and expanded
body sizes. The checked footer and original frame identify the two raw
level sections and signed PLAIN suffix. Byte caps apply before slicing.
[Required V1 profile](parquet-list-required-container.md) · [Pinned V2 header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L788)

## Header counts and readback

- `num_values` is the number of original level slots, including empty
  list markers and null children. The repetition and definition streams
  agree with this count and the column metadata.
- `num_rows` is the number of repetition-zero markers. The page starts
  at a row boundary. Its reconstructed row count agrees with both the
  page header and the footer row group, with distinct errors for disagreement.
- `num_nulls` counts definition-zero empty list markers and definition-one
  null children. Every other admitted slot has definition two and consumes
  one signed little-endian INT32. The untouched suffix has exactly
  `4 * (num_values - num_nulls)` bytes.

The file proof binds the original chunk and header to these counts, preserves
ordered children and distinguishes a present empty list from an item that
is null. The reused Arrow writer certifies the original field names,
nonnullable LIST parent, nullable child and ordered batches through exact
native V5 EOS. A framing refusal retains its original typed cause and
group ordinal. A page-body refusal also carries its frame ordinal and
absolute header offset. Either retains all earlier completed batches in
the source trace and takes precedence over writer admission.

## Independent fixture

PyArrow 26.0.1 writes the native two-group uncompressed V2 file. Thrift
independently checks the original repetition flags and LIST annotation,
raw page and section extents, all three counts and the signed value bytes.
PyArrow verifies the output schema and nested values. A separate check
accounts for every IPC frame through EOS.

The labeled assembled positive control omits the second page's
`is_compressed` flag and repairs its framing. The negative controls
independently vary each header count and the footer row count. They also
check invalid level geometry, a leading continuation, definition 3, and a
short or surplus PLAIN word. Each of the late source controls uses a zero
IPC row cap to exercise source-error precedence.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Hashes and observations](../../scripts/parquet-list-required-container-v2/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-required-container-v2/Oracle.py "$replay" |
  diff -u scripts/parquet-list-required-container-v2/observations.txt -
```
