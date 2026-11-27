# Opt-in Snappy PLAIN V2 Parquet LIST to native Arrow IPC

`Parquet.ListFile.Multi.Snappy.convertV2` selects Data Page V2 for the same
canonical nullable LIST of nullable signed INT32 children. It uses codec
one from the original checked column and accepts raw encoding tag zero on
every page. `Snappy.convert` selects V1, and the original uncompressed
LIST entry points select codec zero. Each conversion requires its selected
page version throughout. Dictionary pages and offsets, mixed page
versions, and other nested shapes are outside this profile.
[Canonical file profile](parquet-list-file.md) · [Snappy V1 profile](parquet-list-snappy-v1.md)

The original column chunk is completely framed on the checked immutable
snapshot. An optional CRC is verified over each frame's complete stored
payload, including both raw level sections and the stored values. The
repetition and definition byte lengths independently bound two raw Hybrid
streams, with no V1 length words. Their sum must fit both advertised
page sizes before subtracting it. The stored and expanded suffix extents
are exact. The resolved `is_compressed` flag selects the original raw
suffix when false and a single exact Snappy member when true. An omitted
flag takes the wire default of true. The page and cumulative expansion
caps charge the raw levels and expanded values together.
[Pinned V2 Thrift header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L788) · [Stored CRC](parquet-page-crc32.md)

The level streams yield exactly `num_values` ordered slots. The checked
row count is the number of repetition-zero slots. The checked null count
includes every slot without a physical INT32 word, including null lists,
empty lists, and null elements. The exact signed PLAIN suffix has four
bytes per remaining slot. A nonempty V2 page must start at repetition
zero even when there is an open list in the preceding state. Repetition
one still continues a list within a page. The group walker feeds the
original page events in order, and the first event of a nonempty V2 page
starts a new row. Footer row and chunk slot totals must match. There is no
group-level claim about optional null statistics.

`prepareV2_wire` and `readV2Frame_wire` tie the original stored and checked
CRC slice to the raw level and scalar witnesses. `readV2Group_counts` proves
that the original page headers sum to the selected footer's value and row
totals and to the reconstructed null-slot count. `convertFor_readback`
at `.v2` relates those original frames to the ordered nullable batches
and exact native EOS.

The complete chunk framing phase retains its original typed group error.
Once framing succeeds, the earliest body or transition failure retains
its zero-based page ordinal and absolute header offset. The first failed
group retains the completed preceding groups. Source failure has
precedence over IPC limits and yields no IPC carrier.
[Public theorem headers](../../Silmaril/Formats/Parquet/ListFile/Multi/Snappy/Thms.lean)

## Independent reproduction

PyArrow 26.0.1 generates two native files, one with checksums and one
without. Both contain two groups with four V2 pages per group and both
suffix flags. One compressed suffix expands from 13 to 156 bytes. The
separately assembled default-flag control omits the last page's true flag
and retains its stored CRC and body. Thrift 0.25.0, zlib and PyArrow
independently inspect the exact frame boundaries, level partitions,
counts, signed words and CRCs. PyArrow reads the native and assembled
positive inputs and the Lean-written IPC.

The two late CRC mutations separately touch uncompressed levels and
compressed values. Assembled refusals test oversized level geometry, a
wrong in-range level split, a forbidden leading continuation after an
open list, and incorrect page and footer counts. Every late refusal and
the cumulative expansion control preserve the first batch even with an
IPC row limit of zero.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Exact hashes and observations](../../scripts/parquet-list-snappy-v2/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.V2Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.V2Examples
python3 scripts/parquet-list-snappy-v2/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-v2/observations.txt -
```
