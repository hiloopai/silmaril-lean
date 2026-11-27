# Opt-in selected GZIP-column PLAIN V2 Parquet DATE

`Date.Leaf.Gzip.V2.readAll` and `Date.Leaf.Gzip.V2.toIpc` select one flat
required or optional INT32 DATE leaf by zero-based physical ordinal.
The strict selected binding checks the original raw DATE annotation
and path. Each selected chunk has Parquet codec 2 (GZIP) and PLAIN
data page V2. Dictionary and index offsets are typed refusals. The
prior GZIP entry point continues to admit V1 pages under its existing
contracts.
[Selected DATE binding](parquet-date-selected-leaf.md)
· [GZIP PLAIN V1 profile](parquet-date-gzip-v1.md)
· [Parquet 2.14.0 compression](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md)
· [Pinned Parquet IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

The stored payload comprises the original definition-level bytes
followed by the stored value suffix. Flat DATE requires zero
repetition-level bytes. The definition levels are passed directly to
the mask reader. The original V2 flag selects either one exact bounded
RFC 1952 member or the exact raw PLAIN suffix. The header parser
resolves an omitted flag to true. Both suffix lengths are derived from
the corresponding whole-page length after checking the level extent
against both declarations.
[RFC 1952](https://www.rfc-editor.org/rfc/rfc1952)
· [Executable profile](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/V2/Defs.lean)

Chunk framing, aggregate byte caps and the declared group slot total
are checked during planning. For each planned page the stored byte
cap and original extent precede the outer Parquet CRC check, when a
CRC is present. This verification precedes the per-page expansion cap,
level splitting and suffix decoding. Compressed suffixes have bounded
controller calls. Planned page failures retain the selected group index,
zero-based page ordinal, original offset and cause. Errors before a page is framed
carry the original group index and shared framing cause. A source failure precedes
writer limits and retains exactly the earlier complete event batches.

`pageWire_exact` binds the stored payload, CRC and independent byte
caps to the exact raw levels, codec-specific suffix and signed PLAIN
values. It relates decoded slot, row, value and null counts to the
original header. `readGroup_wire` concatenates original page slots in
order at the declared group count. `toIpc_readback` gives the exact
descriptor and one Date32 IPC batch per original group through EOS.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/V2/Thms.lean)

## Independent checks

PyArrow 26.0.1 emits genuine optional and required V2 DATE fixtures in
GZIP columns. Both fixtures contain pages with explicit true and false
compression flags. A third genuine fixture reuses the earlier all-raw
V2 control and reads successfully with zero GZIP controller calls.
Thrift 0.25.0 inspects the original footer and page headers. zlib checks
the stored CRC and inner GZIP trailer where applicable. The oracle
independently reads the raw mask, signed values and emitted Date32 IPC.
[Arrow 26.0.1 source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture fingerprints and observations](../../scripts/parquet-date-gzip-v2-oracle/fixtures.json)

Separate malformed controls flip a stored level byte, corrupt a GZIP
trailer while recomputing the outer CRC, and edit level, raw suffix or
expanded suffix extents and declared counts. PyArrow independently rejects both
CRC-damaged groups after reading the preceding one. Thrift edits keep
the original stored extents. Additional controls exercise stored cap
before CRC, CRC before expansion cap, the compressed call budget, and
genuine out-of-profile V1 and V2 dictionary inputs.
[Oracle](../../scripts/parquet-date-gzip-v2-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Thms +Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-v2/Axioms.lean
python3 -I scripts/parquet-date-gzip-v2-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
