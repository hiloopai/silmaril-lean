# LZ4_RAW in recursive signed Parquet V1 and V2

The recursive signed reader admits Parquet codec 7, LZ4_RAW, on
unindexed PLAIN Data Page V1 and V2. The schema supports signed
INT32/INT64, Struct and canonical three-level LIST with at most one
repeated ancestor per leaf. Codec ID 5 is rejected at column binding.
The payload decoder interprets one independent LZ4 block with empty
history. LZ4 frames and the deprecated Hadoop carrier have no reader
route. Dictionary and index admission, the codec-zero pageless
profile, and native UNCOMPRESSED V1 emission keep their existing
contracts.
[Pinned Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

V1 verifies optional CRC against the original stored frame before
expanding the whole body. Its bounded decoded level sections and
signed suffix use the existing V1 reader. V2 checks the same
stored-body CRC and retains the original raw level spans. A true
compression flag selects the original column codec for the suffix.
The false flag uses the original suffix directly, including under
codec 7. Both header sizes must cover the V2 level prefix. The
compressed suffix has an exact input and output extent. The raw
output is bounded by the page cap and checked against the signed
word count before expansion.
[Pinned V2 header and compression flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

The V1 and V2 wire witnesses relate the stored bytes to the selected
`Payload.Decodes` relation and decoded bytes. Signed slot, row start,
null and continuation accounting still uses the common decoder. The
chunk proof preserves original order and gives the header-inclusive
raw size from the same page frames. Direct Events and IPC use those
original group and page witnesses.

## Fixtures and regressions

Pinned PyArrow writes codec 7 in both genuine nested files, with
checksums, unequal sibling page cuts, null and empty Lists, null
elements and signed endpoints. The genuine V2 file includes raw
suffixes with the resolved flag set to false. A separate pinned
liblz4 build checks the raw blocks. Independent Compact, CRC and
level inspection compares the stored bytes, decoded values and
original frame positions with Lean. PyArrow reads the native IPC
streams and raw framing checks exact EOS.

Labeled controls cover codec ID 5, LZ4 framing, malformed blocks,
stored CRC, raw extent, stored and decoded limits, and footer totals.
Both page versions expose the original late malformed-block cause
after a complete group, including under empty projection. IPC reports
the same cause ahead of output limits. A genuine codec-7 pageless
group exercises the strict footer refusal.
[Fixture and liblz4 pins](../../scripts/parquet-recursive-lz4-raw-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-lz4-raw-oracle/Axioms.lean
python3 scripts/parquet-recursive-lz4-raw-oracle/check.py
```
