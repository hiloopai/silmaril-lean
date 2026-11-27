# Selected Snappy V2 Parquet TIMESTAMP dictionary fallback

`Timestamp.Leaf.Fallback.Snappy.V2.convert` opts into Snappy for one
checked modern flat INT64 TIMESTAMP leaf. Each selected chunk needs
one leading PLAIN dictionary frame and a nonempty RLE_DICTIONARY
Data Page V2 prefix followed by a nonempty PLAIN Data Page V2 suffix.
The original data header selects each decoder. Reference pages after
the first PLAIN page fail at their original ordinal and header offset.

The reader uses the strict Snappy V2 header gate and the shared
fallback planner and decoder. The checked selection ties the frame
chain and both data and dictionary offsets to the original footer.
The stored chunk cap, data headers, phase order, and declared group
slot count are checked before expanding the leading dictionary. The
dictionary and data payload checks verify a present Parquet CRC across
the full original stored body before expanding that body. Dictionary
entries are bounded signed PLAIN words from that chunk alone.

V2 definitions remain raw and the repetition extent is zero. The
original flag selects an exact literal or bounded Snappy block for
the value suffix in each phase. Exact hybrid references or PLAIN
signed words, together with the decoded mask and checked null count,
preserve ordered nullable slots across the transition. Header, phase,
and payload validation retain the typed original coordinates of the
first failure within their stage.

The event trace retains the complete earlier group batches, and the
first source group failure precedes Arrow writer admission. Successful
native Arrow V5 IPC reads through EOS with one batch per original
footer group and the exact field name, nullability, time unit,
UTC or local interpretation, and signed nullable ticks. The existing
V1/V2 fallback and strict dictionary-only entry points retain their
admission.

## Independent evidence

Two genuine PyArrow 26.0.1 producer files contain six dictionaries
and eighteen original V2 data frames. Each group has the sequence
RLE_DICTIONARY, PLAIN, PLAIN. Both storage flags occur in both phases
in each file. Nullable UTC nanoseconds use stored CRCs, and required
local microseconds have zero definition bytes and absent CRCs.
Thrift, zlib, PyArrow's Snappy decoder and an independent hybrid reader
check the original headers, CRCs, masks, and signed words. PyArrow
also reads both actual Lean-emitted IPC streams through EOS.

Labeled unchanged-chunk assemblies exercise a late V1 fallback and
a late V2 dictionary-only group. PyArrow reads both assemblies, and
the broader Snappy fallback path reads the V1 assembly. Separate
mutations exercise dictionary, reference and PLAIN CRCs, compressed
reference and PLAIN suffixes, reentry, a PLAIN first data page, and
competing failures. The Lean comparator verifies sixteen typed
refusals and ten exact completed prefixes.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Snappy/V2/Thms.lean) ·
[Strict dictionary V2](parquet-timestamp-snappy-dictionary-v2.md) ·
[Comparator](../../scripts/parquet-timestamp-snappy-fallback-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-fallback-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-fallback-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-snappy-fallback-v2-oracle/check.py
```
