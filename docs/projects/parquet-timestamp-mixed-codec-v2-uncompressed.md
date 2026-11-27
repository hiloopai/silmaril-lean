# Selected four-codec Parquet TIMESTAMP V2 dispatch

`Timestamp.Leaf.MixedCodec.V2.WithUncompressed.convert` opts into
selection of one modern flat INT64 TIMESTAMP leaf whose original
row-group chunks use UNCOMPRESSED (0), Snappy (1), GZIP (2), or
Zstandard (6). Each group reads the original selected footer codec
once. Codec 0 invokes the strict uncompressed V2 dispatcher. The
other codec decision uses the existing three-codec routing helper.
Each codec uses its established PLAIN-only, dictionary-only, and
one-way fallback profiles and frame and payload limits.

Each successful group retains the selected dispatcher's original frame, CRC, and
ordered signed nullable slot witness. Source tracing collects complete
groups in footer order and carries the first failed original group
and its typed nested cause. A source failure takes precedence over
IPC writer admission. Successful native Arrow V5 IPC reads through
EOS and retains the field descriptor, exact counts, and batch boundary
for each original group.

For inputs with no selected codec-0 group, the four-codec reader has
the same complete result as the three-codec reader after embedding
the old errors. The Events batches and termination agree under the
same embedding, and successful IPC bytes are identical. This includes
files with an unsupported codec, source lookup or open failures, and
writer failures. Existing converter entry points retain their own
admission rules.

## Independent evidence

Genuine pinned PyArrow producers supply all twelve codec and encoding
profile pairs. Two labeled mixed files assemble those original chunks
with nullable UTC nanoseconds or required local microseconds. Thrift
and zlib check the selected original span, page offsets, raw stored
bytes and present CRCs. PyArrow independently reads both mixed files
and ten actual Lean-emitted streams. The two prior assemblies also
produce IPC byte for byte equal to the three-codec entry point.

The comparator checks sixty selected group reads, fifteen typed refusal
controls, and eleven complete prefixes. The controls include original
late CRC failures in all four routes, competing errors, the codec-0
dictionary chunk limit, and embedded predecessor failures for CRC,
page version, unsupported codec, source, and writer limits.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/MixedCodec/V2/WithUncompressed/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-mixed-codec-v2-uncompressed-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-mixed-codec-v2-uncompressed-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-mixed-codec-v2-uncompressed-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-mixed-codec-v2-uncompressed-oracle/check.py
```
