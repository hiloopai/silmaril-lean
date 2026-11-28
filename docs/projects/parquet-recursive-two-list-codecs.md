# Checked column codecs for two-LIST Parquet

The reader accepts a single signed INT32 or INT64 leaf under two
canonical LISTs in unindexed PLAIN V1/V2 chunks. Each row group binds
its codec from its own original column metadata.

| Codec | Parquet ID | Checked payload |
| --- | ---: | --- |
| UNCOMPRESSED | 0 | Exact raw bytes |
| SNAPPY | 1 | One exact raw Snappy block |
| GZIP | 2 | One RFC 1952 member with exact input and output, including CRC and ISIZE |
| ZSTD | 6 | One exact dictionary-free frame in the existing checked block, literal and sequence profile |
| LZ4_RAW | 7 | One exact raw LZ4 block |

Codec 5 and codec 4 remain outside this profile. The reader uses the
same checked GZIP member controller, Zstd frame adapter and LZ4_RAW
block decoder as the recursive one-LIST reader. GZIP defaults to
65,536 controller calls per reached member. Zstd defaults to an
8 MiB window and 43,690 commands per block. Both stored and
decoded byte caps apply independently.
[LZ4_RAW](parquet-recursive-lz4-raw.md) · [GZIP](parquet-recursive-gzip.md) · [Checked Zstd profile](parquet-recursive-zstd.md)

V1 checks the optional CRC over the original stored body before
expanding the whole body. V2 checks the same stored CRC, keeps the
original raw repetition and definition spans, and expands only the
original suffix when the resolved flag selects the column codec.
A false flag reads the raw suffix directly, including under zero GZIP
controller calls or zero Zstd window and command budgets. The shared
witnesses retain the exact header-inclusive stored and decoded footer
totals, slot, row and null counts, V1 continuation and V2 closure.

The existing Rows, Events and IPC routes use these witnesses. Direct
Events keeps the complete prefix and original addressed source error
under both selections. IPC gives the source error precedence over its
output limits.
[Two-LIST schema and cursor](parquet-recursive-two-list.md) · [Events](parquet-recursive-two-list-events.md) · [IPC](parquet-recursive-two-list-to-ipc.md)

## Reproduction

The pinned oracle checks genuine PyArrow V1 and V2 inputs for LZ4_RAW,
GZIP and Zstd at both signed widths. Independent Compact, Hybrid,
signed-word, liblz4, zlib and libzstd inspection checks original CRC,
exact payload and level spans, and both byte totals. The authored
mixed-group file copies original serialized frames in codec order
0, 7, 1, 2, 6. Labeled edits also check raw V2 bypass and Zstd content
checksums. PyArrow reads native Lean IPC through exact EOS.

Typed controls distinguish deprecated LZ4, byte caps, GZIP controller
and trailer failures, Zstd dictionary IDs, windows, commands and
checksums, trailing or concatenated input, and separately wrong stored
and decoded footer totals. Late LZ4, GZIP and Zstd failures retain
the earlier groups through empty projection. The late Zstd checksum
control exercises that property across four differently encoded groups.
[Producer, source and IPC pins](../../scripts/parquet-recursive-two-list-more-codecs-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-more-codecs-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-more-codecs-oracle/check.py
~~~
