# Raw Brotli in recursive signed Parquet V1 and V2

The recursive signed unindexed PLAIN reader accepts codec 4 when
`Chunk.Limits.brotliRaw` contains explicit window and meta-block limits.
The default binding refuses codec 4 at the original column. Rows,
direct Arrow Events and native IPC take this setting through
`Rows.Limits.chunk`. The schema remains signed INT32/INT64, Struct
and canonical three-level LIST with at most one repeated ancestor
per leaf. Codec-zero pageless admission and native UNCOMPRESSED V1
emission retain their existing contracts.
[Pinned Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

The checked adapter accepts a standard Brotli window, zero or more
non-last uncompressed meta-blocks, and an empty last meta-block.
Alignment fill must be zero and the stream must end in its original
slice. Entropy-coded and metadata meta-blocks are refused. Window
bytes and meta-block work are checked independently of input and
output extents. The work limit counts the empty terminal block.
The payload proof binds the actual configured limits and exact
decoded extent to the original bytes.
[Raw Brotli stream format](https://www.rfc-editor.org/rfc/rfc7932#section-9)

The recursive reader calls `ScalarPage.BrotliRaw.decodePayload` for
whole V1 bodies and compressed V2 value suffixes. It checks the
Parquet CRC of the entire stored body before either decode. V2
retains the original repetition and definition spans and takes the
original value suffix directly for a false flag. That branch uses
zero Brotli work. Page and chunk witnesses retain the original
signed slots and row counts, the V2 null count, V1 continuation and
header-inclusive footer sizes.
[Pinned V2 header and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

## Fixtures and regressions

Pinned PyArrow writes a genuine nested quality-zero V1 file containing
raw Brotli meta-blocks. Its genuine V2 counterpart stores every suffix
raw under codec 4 and decodes with a zero work limit. Genuine
quality-five V1 and V2 files exercise the entropy-coded refusal.
The labeled multi-page V1 and V2 files start from independently
checked UNCOMPRESSED originals. They preserve the decoded bodies and
original level words, including the V2 raw prefixes, and rebuild
stored CRCs, offsets and header-inclusive sizes around authored raw
Brotli streams. Pinned libbrotli and independent bit inspection check
the exact byte output and stream end. PyArrow reads the emitted Lean
IPC, and raw framing checks exact EOS.

Labeled failures cover stored CRC, exact extent, window and work
limits, truncation, padding, metadata, trailing input and footer size.
A late stream error in either page version preserves the complete
group and its original coordinates through empty projection and ahead
of IPC output limits. A zero-work run likewise preserves the raw V2
prefix before it reaches a compressed suffix. A genuine codec-4
pageless source exercises the strict footer refusal.
[Fixture and libbrotli pins](../../scripts/parquet-recursive-brotli-raw-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-brotli-raw-oracle/Axioms.lean
python3 scripts/parquet-recursive-brotli-raw-oracle/check.py
```

The oracle builds the pinned libbrotli reference using CMake and a C
compiler.
