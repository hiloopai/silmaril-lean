# Selected Zstandard V2 Parquet TIMESTAMP dispatch

`Timestamp.Leaf.Zstd.Dispatch.V2.convert` opts into codec 6 for one
required or optional modern flat INT64 TIMESTAMP leaf. It visits the
selected chunk of each row group in footer order. The selected
column's dictionary offset routes dictionary-free chunks to the
strict PLAIN V2 reader. For a dictionary-backed chunk, the reader
frames the selected original bytes once. Any PLAIN V2 data header in
that chain selects the fallback planner. Otherwise the dictionary-only
planner requires RLE_DICTIONARY throughout. The chosen planner and
decoder use those frames and return the same typed result as the
corresponding strict reader.

The strict planners enforce the leading PLAIN dictionary, original
footer offsets, V2 encodings, declared row totals, and stored and
expanded byte limits. Fallback requires a nonempty reference prefix
and a nonempty PLAIN suffix, and rejects reference reentry. The same
dispatch limits supply the PLAIN branch's stored and expanded caps
and the dictionary branches' stored, expanded and entry caps.
Whole-chunk framing and admission precede page decoding. A present
Parquet CRC covers the original stored payload. V2 levels remain raw
and the storage flag selects an exact literal or compressed value
suffix. Compressed suffixes and dictionaries use one bounded
dictionary-free Zstandard frame with the supported block and
checksum profile. The three standalone entry points retain their
strict admission rules.

Successful native Arrow IPC reads through EOS with the selected field
name, nullability, unit, UTC or local semantics, and exact signed
nullable ticks, in one batch per original group. A failed source
group retains the complete earlier event batches, and the converter
returns the first source group failure before writer admission. The
underlying strict error retains its original page ordinal and
absolute offset when the stage identifies a page.

## Independent verification

PyArrow 26.0.1 natively writes two codec-6 files with alternating
dictionary-only and fallback groups, and two PLAIN-only producers.
The UTC nanosecond file is optional and includes nulls and both signed
INT64 endpoints. The local microsecond file is required. Two labeled
assemblies insert the unchanged PLAIN-only chunks between original
groups and update footer offsets and totals. PyArrow reads all
assembled groups independently. Thrift, zlib and libzstd 1.5.7 verify
original frame extents, codec, stored CRCs, encodings, flags, masks
and exact signed slots. Both V2 storage flags occur in each admitted
data phase. PyArrow reads the four actual Lean-emitted IPC streams.

Separately pinned mutations check late CRC, Zstandard magic, flag,
reference width and reentry errors, including competing group
failures. Genuine V1 and Snappy controls exercise the profile's
version and codec boundaries. The Lean comparator checks 20 group
classifications and their strict values, 22 typed refusals and 10
complete earlier prefixes.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Zstd/Dispatch/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-zstd-dispatch-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-zstd-dispatch-v2-oracle/fixtures.json) ·
[Zstandard frame profile](zstd-huffman-frame.md) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-zstd-dispatch-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-zstd-dispatch-v2-oracle/check.py
```
