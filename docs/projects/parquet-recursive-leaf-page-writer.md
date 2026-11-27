# Recursive signed Parquet V1 page writer

`Parquet.RecursiveSchema.Repeated.Chunk.Writer.emit` takes one compiled
physical leaf, a starting chunk state and ordered `Rows.Atom` values. The
profile is signed INT32 and INT64, UNCOMPRESSED PLAIN Data Page V1, under the
existing recursive schema compiler's limit of one repeated ancestor per leaf.
An unindexed continuation uses the live List state carried from the
preceding page. Slot and row coordinates start at the supplied state.

The writer emits the repetition section before the definition section.
Each positive-width section carries a little-endian INT32 length followed
by one singleton RLE run per original level. Zero-width sections are
omitted. Only present values contribute little-endian signed words.
The Compact header declares the slot count, both exact body sizes, PLAIN
value encoding and RLE level encodings. The optional CRC32 covers the
exact stored body. An empty page retains its supplied state. Its
positive-width level sections have zero length.

The writer measures the original slots, row starts, encoded level bytes
and body against the reader's limits before constructing the body.
It checks the Compact header and complete frame budgets as well.
Invalid level pairs, contradictory classifications, missing or extra
words, wrong signed widths and a continuation without a live List
are typed refusals.

`serialize_construction` proves the emitted page has the specified body
and Compact header under the measured limits. `certify_readback` derives
the original reader's `PageWire` from its checked read of the emitted
carrier, including exact level and word consumption. The recovered
levels, classifications and signed words equal the input's, and the
checked frame consumes the entire carrier. `Readback.state_counts`
separates the slot count from the number of repetition-zero row starts.
`emit_wire` gives both witnesses for successful emission. This API
produces individual page frames. Chunk packing, file footer generation
and the IPC-to-Parquet file bridge are later layers.

## Interoperability checks

The oracle uses the predecessor's pinned PyArrow sources and labeled
unindexed mid-row edit. Lean projects the checked logical rows to atoms,
partitions them at the original page cuts and writes 36 native page
frames. The independent Thrift and hybrid readers check header fields,
CRC, level sections and the exact signed suffix, including both signed
widths' endpoints. Python splices the emitted pages into test-only
carriers with the source schema and adjusted chunk spans. Pinned PyArrow
checks the original ordered row groups in each assembled carrier,
including the continued List. Two empty frames are checked separately
as pages. Sixteen typed checks cover atom, limit, CRC and extent refusals.

The fixture pins include each emitted page series in original group,
column and page order, the two separate empty frames and the four
test-only carriers. The source hashes and CPython, PyArrow and Thrift
versions are inherited from the predecessor manifests.

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-leaf-page-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-leaf-page-writer-oracle/check.py
```
