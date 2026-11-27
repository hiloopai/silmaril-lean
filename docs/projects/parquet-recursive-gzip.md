# Single-member GZIP in recursive signed Parquet V1 and V2

The recursive signed reader admits Parquet codec 2 for unindexed PLAIN
Data Page V1 and V2. The schema supports signed INT32/INT64, Struct and
canonical three-level LIST with at most one repeated ancestor per leaf.
Dictionary and index admission, the codec-zero pageless profile and
native UNCOMPRESSED V1 emission retain their existing contracts.
[Pinned Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

V1 decodes the whole stored body. V2 retains the original repetition
and definition spans and uses the resolved compression flag on the
value suffix. A false flag uses the original suffix directly, even
under codec 2. Both routes check optional Parquet CRC on the original
stored body before decoding any GZIP bytes. The existing payload
controller then checks one RFC 1952 member, including its own CRC32 and
ISIZE, and requires exact output and exhausted input. Trailing bytes
and concatenated members return the typed trailing-input error.

`Chunk.Limits.gzipCalls` defaults to 65,536 controller calls per reached
GZIP member, following the TIMESTAMP scalar reader convention. Call
fuel is independent of the stored and decoded byte limits. Exhaustion
returns the reached page's `payload gzipIncomplete` error, including if
the caller sets zero. A raw V2 suffix needs no GZIP calls. The existing
Rows, direct Events and native IPC entry points receive this setting
through `Rows.Limits.chunk`.
[Pinned V2 flag and sections](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)
[GZIP member and trailer format](https://www.rfc-editor.org/rfc/rfc1952#section-2.3.1)

The page wire witnesses retain both the successful call at the supplied
limits and the selected payload relation. For GZIP this relation
recovers exactly one completed member and an empty suffix. The shared
proofs still account for signed values, slot and row counts, V2 nulls,
V1 continuation, and header-inclusive footer sizes on the original
page chain. Group, column, page, byte and state coordinates remain
attached to reached errors.

## Fixtures and regressions

Pinned PyArrow supplies genuine nested multi-group GZIP V1 and V2 with
checksums and unequal sibling page cuts. The V2 file includes genuine
raw suffixes under codec 2. Independent Compact and level inspection
uses standard zlib in GZIP mode, requiring completed decoding, exact
output length and empty unused input for each admitted compressed
page. The oracle independently inspects the stored page CRC and the
GZIP trailer. PyArrow and raw IPC frame inspection check both emitted
Lean streams through exact EOS.

Labeled controls separate stored CRC from member CRC and ISIZE, require
strict refusal of trailing bytes and a second valid member, and cover
decoded size, both byte caps, footer totals, and controller exhaustion
at zero and one call. A genuine GZIP pageless source exercises the
strict footer refusal. The late trailer failure preserves the completed
group and exact terminal through empty projection and ahead of output
limits. A zero-call V2 projection also preserves the raw group prefix
before the next compressed page exhausts its call budget.
[Fixture pins](../../scripts/parquet-recursive-gzip-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-gzip-oracle/Axioms.lean
python3 scripts/parquet-recursive-gzip-oracle/check.py
```
