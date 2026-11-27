# Opt-in mixed-page Snappy PLAIN Parquet LIST

`Parquet.ListFile.Multi.Snappy.Mixed.convert` reads the canonical nullable
LIST of nullable signed INT32 children. The checked local column has
codec one and admits PLAIN V1 and V2 frames in their original order.
The pinned Parquet format explicitly permits interleaved page types in
one column chunk. Its Thrift IDL assigns V1 and V2 separate data-page tags
and selects the matching header for each page. The mixed converter
dispatches on that checked tag. The existing `Snappy.convert` and
`Snappy.convertV2` select one page version explicitly. The original
uncompressed LIST APIs select codec zero.
[Pinned format hierarchy](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#glossary) · [Page types](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L681-L686) · [Per-page header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L830-L863)

The original frame and stored CRC checks run through the existing page
decoders. V1 expands a complete Snappy body and consumes both original
length-prefixed Hybrid level sections and its exact PLAIN suffix. V2
checks the two raw level extents and selects the raw or Snappy suffix
from the resolved flag. Its page slot, row and null counts describe the
decoded data. The mixed walker uses the same slot accounting and the
same page-wide and file-wide expansion budgets. Raw V2 level bytes count
toward both expansion caps.
[Snappy V1 wire and counts](parquet-list-snappy-v1.md) · [Snappy V2 wire and counts](parquet-list-snappy-v2.md)

V2 pages start and end on row boundaries under the pinned V2 rule.
A V1 page may continue a live list across a V1-to-V1 cut when no
OffsetIndex is advertised. The walker retains a pending row boundary
after every V2 frame, including across empty V1 frames, until the next
nonempty page starts a row. A nonempty V2 page checks its own leading
repetition level. The checked state reconstructs null lists, empty
lists, null children and signed values in original order.
[Pinned V2 row-boundary rule](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L742-L766)

`Mixed.readFrame_wire` ties each admitted page to its original version's
wire relation. `Mixed.v2_startsAtBoundary`,
`Mixed.following_v2_startsAtBoundary` and the `Boundaries` witness
establish the entry and trailing V2 rules. `Mixed.readGroup_wire` ties
the original selected chunk and exact framed page order to reconstructed
rows, the sum of the original header slot counts and footer row totals.
The V2 witnesses retain exact per-page null counts.

Chunk framing runs before ordered body checks and carries the existing
typed group framing error. Once framing succeeds, the first failing page
carries its original ordinal and absolute header offset.
`Mixed.convert_first_error` retains the completed preceding batches and
puts the original source error ahead of native IPC limits. Only the
successful full source can reach native IPC publication.
`Mixed.convert_readback` binds that publication to the same schema,
groups, ordered nested nullable rows and exact EOS. Dictionary pages
and other nested shapes are outside this profile.
[Public theorem headers](../../Silmaril/Formats/Parquet/ListFile/Multi/Snappy/Mixed/Thms.lean)

## Independent reproduction

PyArrow 26.0.1 chooses a page version for the whole writer. The pinned
mixed fixtures are assembled using independently generated V1 and V2
pages, with fresh Thrift footer extents and counts. The continuation
fixture additionally uses the previously assembled V1 continuation
page and follows that continued row with V2. Apache Thrift 0.25.0 checks
the page tags, exact extents and original counts. A separate Hybrid
level walk, PyArrow's Snappy codec and zlib inspect the actual slots,
signed values and stored CRCs. PyArrow reads both assembled Parquet
files and the Lean-written native IPC, and detects late CRC mutations
in either page version.

The PyArrow comparison covers the two pinned valid arrangements and
the CRC mutations. Lean checks the authored transition refusals,
including both directions of a V2 boundary and a continuation through
an empty intervening V1 page. The limit and failure controls check that
the first group stays in the trace under a rejecting IPC row budget.
[Pinned PyArrow writer option](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/python/pyarrow/parquet/core.py#L839-L843) · [Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Exact hashes and observations](../../scripts/parquet-list-snappy-mixed/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Examples
python3 scripts/parquet-list-snappy-mixed/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-mixed/observations.txt -
```
