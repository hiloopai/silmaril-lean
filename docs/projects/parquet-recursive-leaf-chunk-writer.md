# Recursive signed Parquet V1 leaf chunk writer

`Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.emit` takes one compiled
physical leaf, a declared row count and an ordered partition of the
original row-projection atoms into pages. It emits one unindexed
UNCOMPRESSED PLAIN Data Page V1 chunk for signed INT32 or INT64. It
inherits the compiler's limit of one repeated ancestor per leaf.
Each page uses the same optional stored-body CRC32 policy.

The initial cursor is at byte, page, slot and row zero with a closed List.
Every following page inherits the previous page's state. A live List
can continue at the next page, and only repetition-zero slots count as
row starts. A writer refusal retains the page ordinal and original
page cause. The strict reader retains its typed cursor and cause.

A positive-row partition contains at least one page and every page
contains at least one slot. In a compatibility probe, PyArrow recovered
different rows when an empty page interrupted a continued List.
A zero-row group uses exactly one empty
Data Page V1 per leaf. That page has zero value slots and still includes
its header. It omits zero-width level sections and uses a zero length
prefix for each nonzero-width section. The emitted chunk therefore
always has a first data-page offset of zero relative to its own start.

The admission guard bounds page count, total slots, and declared rows
before serializing. Each page receives the unused portion of the
chunk byte budget, which counts headers and payloads. Slot and row
state are cumulative. Limits on a single header, body and level section
still apply to each page. The returned compressed and uncompressed
sizes are equal and include all headers. Footer construction can add
the eventual file start to the relative page and data-page offsets.

## Guarantees

`serialize_construction` binds every emitted piece to the original
partition, its incoming and outgoing state, and the enforced limits.
`assemble_ordered` gives exact byte concatenation. The same strict
`Chunk.walk` used after footer binding reads the complete emitted
carrier once. `certify_readback` binds the returned relative spans
and ordered observations to the original bytes and exact terminal
cursor. It recovers the declared row total and all level slots.
`PageAgreement.original` preserves both level words, their
classifications, and every signed value, page by page.
`PageAgreement.checksums` ties each original observed header to the
chosen optional CRC policy. `first_data_page` binds the returned offset
to the first checked page header. `emit_wire` gives the construction and
readback witnesses for successful emission.

The production certificate is for the strict lower-level walk on the
exact chunk carrier. Full file readback requires a checked snapshot and
positional footer binding. Footer emission and the reverse IPC-to-Parquet
file bridge are subsequent layers.

## Interoperability checks

The oracle checks 24 emitted chunks spanning 40 pages. Pinned
PyArrow inputs and labeled source assemblies cover single and
multiple pages, unequal sibling cuts, signed endpoints, an authored
mid-row continuation, optional CRC and groups of 3, 0 and 2 rows.
Thrift and independent hybrid-level inspection check actual Lean bytes
and compare the returned frame index and metadata counts.
Python builds four test-only containers with the emitted chunks and
adjusted offsets from the source footers. Pinned PyArrow reads their
ordered logical rows. Lean also opens those containers and checks the
rows through the original snapshot, chunk and row-group readers.
Fourteen typed controls cover aggregate caps, invalid partitions,
declared row mismatches, closed continuations and a late wrong-width
value.

The fixture manifest pins each concatenated chunk series in row-group
and column order, plus the four test-only containers. Source hashes and
producer versions are inherited from the predecessor manifests.

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-leaf-chunk-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-leaf-chunk-writer-oracle/check.py
```
