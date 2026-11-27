# Multi-page uncompressed V2 required Parquet LIST

`ListFile.RequiredContainer.V2.Multi.convert` is an opt-in reader for
one canonical required LIST of nullable signed INT32. It binds the original
footer-selected column to the ordered frame chain on the same immutable
file. Each chunk uses codec UNCOMPRESSED and CRC-free PLAIN Data Page V2.
Both resolved suffix flags select raw bytes under codec zero. The singleton
V1, uncompressed V2, and Snappy V2 readers retain their original admission.
[Singleton V2 contract](parquet-list-required-container-v2.md)

Each nonempty page must start with repetition zero. The V2 Thrift contract
requires pages to start at row boundaries, so a page beginning with a
continuation is rejected even if the previous page left a list open.
The shared stitcher handles transitions within a page and consumes the
original frames in order. It preserves present empty lists and ordered
nullable children. All parent lists are required.
[Pinned V2 header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L788)

- The two raw level streams each consume exactly `num_values` slots.
  The sum of those page counts equals the original column metadata count.
- Each page's `num_rows` equals its repetition-zero count. The summed
  page row counts equal the reconstructed row count and the footer group count.
- Each page's `num_nulls` counts zero-value slots, including empty-list
  markers and null children. The sum equals the zero-value slots across the
  reconstructed group. The footer supplies no corresponding group null count.
- Definition two consumes one signed PLAIN word. The exact original scalar
  suffix has `4 * (num_values - num_nulls)` bytes.

Page body, level, framing, group-slot and group-row caps are checked. The
group's entire original frame chain is checked before page bodies are
decoded. A framing refusal retains its typed cause. Decode and stitch
refusals retain the original group and frame ordinals and absolute header
offset. The source trace retains completed earlier groups ahead of any
writer admission, with no IPC bytes on source failure. On success, the
native V5 reader recovers the original names, required parent, nullable
child, and one ordered batch per group through exact EOS.

## Independent verification

Pinned PyArrow produces the genuine uncompressed file with two row groups
and three V2 pages in each. Thrift checks the footer and each original
header and section extent. Independent level and PLAIN decoding account
for the three counts, empty lists, null children, and both INT32 endpoints.
PyArrow reads Lean's native IPC output with the original schema and rows.
The comparator accounts for every IPC frame through EOS.

Labeled assembled controls change page and footer totals or remove or
append one scalar word. Labeled mutations change an original page's
starting repetition. One mutation leaves a valid live list from the
preceding page. A second control corrupts two page starts and checks that
the earlier one is reported. A separate level mutation attempts to
continue an empty list within a page. The controls set a zero IPC row cap and
require the original earlier batch and typed source error.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Hashes and observations](../../scripts/parquet-list-required-container-v2-multi/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-required-container-v2-multi/Oracle.py "$replay" |
  diff -u scripts/parquet-list-required-container-v2-multi/observations.txt -
```
