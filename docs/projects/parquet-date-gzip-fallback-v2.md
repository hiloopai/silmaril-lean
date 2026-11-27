# Selected GZIP DATE V2 fallback into native Date32 IPC

`Parquet.Date.Leaf.Fallback.Gzip.V2` selects a flat INT32 DATE leaf by physical
ordinal in the original checked snapshot. Each admitted group has one leading
PLAIN dictionary followed by a nonempty RLE_DICTIONARY prefix and a nonempty
PLAIN suffix of V2 data pages. The dictionary keeps the whole-body GZIP
representation and decodes to signed little-endian INT32 entries. The same
one-way phase check used for V1 preserves the original frame order, offsets
and earlier header errors. [Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/V2/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/V2/Thms.lean)

The reader checks the original chunk extent, cumulative declared expansion,
and row total before decoding bodies. It verifies each full stored body and
its CRC when present. A V2 body splits at the original definition-level
extent, with zero repetition bytes. Its raw levels feed the required or
nullable layout from the selected schema. When the flag is true, only the
suffix expands as one exact bounded GZIP member. When the flag is false, the
suffix bytes are used directly at their checked size. The shared
`Gzip.V2.prepareFor_frame` law covers both branches for either encoding. The
mask and counts agree with ordered checked dictionary references or signed
PLAIN words. [Shared V2 law](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/V2/Thms.lean) ·
[Parquet page headers](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Parquet GZIP profile](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#gzip)

Successful native Date32 IPC keeps the descriptor and all ordered nullable
signed days in one batch per original footer group through exact EOS. A
group failure retains complete earlier groups and its original index and
cause. Failures after framing retain the original page ordinal and header
offset. Rejected headers carry the framing cause at the original footer
group index. Source errors precede IPC writer limits. The new profile is an explicit
entry point and existing admission rules remain in effect.

## Pinned comparison

Three genuine PyArrow files exercise both compression flags in dictionary
references and in PLAIN suffixes, nullable and required masks, signed
endpoints, and a selected DATE leaf beside unannotated INT32. Thrift and zlib
independently inspect original frames and CRCs and verify the flag-dependent
suffix and raw level extents. PyArrow independently reads back native Lean
IPC. Native tests re-decode each admitted data page with a zero GZIP call cap
to test the flag selection. Mutated header and integrity probes are labeled,
including the assembled final suffix with a second GZIP member.
[Oracle](../../scripts/parquet-date-gzip-fallback-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-fallback-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-fallback-v2/Axioms.lean
python3 -I scripts/parquet-date-gzip-fallback-v2-oracle/check.py
```
