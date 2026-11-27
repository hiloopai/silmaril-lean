# Selected Zstandard dictionary V2 Parquet TIMESTAMP

`Timestamp.Leaf.Dictionary.Zstd.V2.convert` opts into codec 6 for one
required or optional modern flat INT64 TIMESTAMP leaf. Each selected
footer group contains one leading PLAIN dictionary and one or more
RLE_DICTIONARY Data Page V2 frames. The selected snapshot, original
dictionary and data offsets, and original contiguous frame chain
tie every reference to its chunk's own dictionary.

The reader checks the stored chunk budget, the sum of declared expanded
bytes including the dictionary, every data header, and the declared
group slot total before expanding the dictionary. The dictionary's full
stored payload has a separate entry and byte budget. Its present
Parquet CRC is verified before decoding one exact Zstandard frame
and one signed INT64 word per declared entry.

A present data-page CRC covers the whole original stored body. The
raw definition bytes supply the checked presence mask. There are zero
repetition bytes. The V2 compression flag selects a literal reference
suffix or one bounded Zstandard frame, and both suffix sizes are
checked after subtracting the original definition extent. The hybrid
reference stream has an exact width, extent and present count. Its
ordered lookups reconstruct the original nullable signed slots.

The compressed path uses the same dictionary-free Zstandard frame
decoder as the PLAIN route, with a strict match distance below the
window size and defaults of 8 MiB window and 43,690 commands per block.
The frame content checksum is verified when present. The checked
reference and PLAIN-only readers each retain their own admission
contracts. [PLAIN V2 profile](parquet-timestamp-zstd-v2.md) ·
[Shared Zstandard frame limits](zstd-huffman-frame.md)

Native Arrow V5 IPC reads back through EOS with the selected name,
nullability, original tick unit, UTC or local interpretation and one
batch per footer group. After group planning, the first failing data
page keeps its original page ordinal, absolute header offset and
typed cause. A source group failure keeps the completed earlier batches
in the event trace and reaches the converter before writer admission.

## Independent evidence

Two genuine PyArrow 26.0.1 files exercise nullable UTC nanoseconds with
stored CRCs and required local microseconds without stored CRCs. Each
has three distinct dictionaries and both raw and compressed reference
suffixes. Thrift checks original chunk spans, dictionary and page
headers. zlib checks the Parquet CRCs, and libzstd 1.5.7 checks the
exact extents of all compressed suffixes and dictionaries. Independent
little-endian word and hybrid index observations reconstruct the
ordered signed slots. PyArrow consumes the actual Lean-emitted IPC.

Separately labeled mutations exercise CRCs and Zstandard frame magic
in both dictionary and data, both wrong storage flags, row preflight
before dictionary decode, an invalid dictionary tag, and invalid or
out-of-range references. A genuine producer fallback is refused at
its first original PLAIN data header. A competing-fault fixture
checks the earlier failed group and the preceding completed prefix.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Zstd/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-zstd-dictionary-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-zstd-dictionary-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-zstd-dictionary-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-zstd-dictionary-v2-oracle/check.py
```
