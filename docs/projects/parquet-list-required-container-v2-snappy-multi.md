# Multi-page Snappy V2 required Parquet LIST

`ListFile.RequiredContainer.V2.Snappy.Multi.convert` admits the canonical
three-level required LIST with nullable signed INT32 children, in local
Snappy chunks of PLAIN Data Pages V2. The original checked footer selects
the column. The shared walker consumes the exact frame chain from that
same snapshot, with the group row and level-slot caps checked before any
page body is decoded.
[Singleton Snappy V2 contract](parquet-list-required-container-v2-snappy.md) · [Uncompressed multipage contract](parquet-list-required-container-v2-multi.md)

The shared singleton body reader checks the stored payload extent and byte
cap. It verifies a present CRC over the entire original stored body before
decoding levels or preparing the scalar suffix. An absent CRC is admitted
under the existing verify-if-present policy. Repetition and definition
are raw, with their original header lengths and separate caps. The bounded
suffix is raw for `is_compressed = false`, or decodes as one exact Snappy
member for true. An omitted flag resolves to true. The expanded body cap
and exact signed PLAIN extent apply to each page.

Each nonempty page starts with repetition zero, including after a page
that leaves a live list. The separate checked sums count level slots
against column metadata, row starts against footer group rows, and
zero-value slots against the reconstructed group. An empty LIST marker
and a null child both count as zero-value slots. They remain distinct
in the ordered output. The group witness preserves required parents and
nullable children through one native V5 IPC batch per group and exact EOS.
[Pinned DataPageHeaderV2 specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L788)

The reader checks framing before body decoding. A body or stitch failure
reports the first failing original frame ordinal and absolute header
offset. It retains the earlier completed groups on the source trace and
precedes IPC writer admission.

## Independent verification

PyArrow 26.0.1 produces two native two-group files with three V2 pages
per group, with and without stored CRCs. Both suffix flags occur in the
second group of each file. Independent Compact Thrift, zlib CRC, Hybrid
level decoding and PyArrow Snappy inspect every original extent and the
separate counts. PyArrow reads the actual Lean IPC, including empty lists,
null children and both INT32 endpoints. The comparator accounts for every
IPC frame through EOS.

The assembled positive control omits the final compressed page's flag.
The negative controls mutate raw levels and raw or compressed values
under the original CRC, corrupt two pages to check their error order, and
use repaired CRCs for malformed level and Snappy suffix cases. Other
assembled controls change the original counts, set a false flag on a
compressed suffix, or insert a late page-start continuation. The source
controls retain the first group even with a zero IPC row cap.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Hashes and observations](../../scripts/parquet-list-required-container-v2-snappy-multi/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-required-container-v2-snappy-multi/Oracle.py "$replay" |
  diff -u scripts/parquet-list-required-container-v2-snappy-multi/observations.txt -
```
