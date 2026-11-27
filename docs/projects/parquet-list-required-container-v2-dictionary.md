# Dictionary-only Snappy V2 required Parquet LIST

`ListFile.RequiredContainer.V2.Snappy.Dictionary.convert` admits the
canonical three-level required LIST of nullable signed INT32 children.
Each selected local Snappy chunk has one leading PLAIN dictionary followed
by one or more RLE_DICTIONARY Data Pages V2. The checked footer's dictionary
and data offsets must point to those original frames. The chunk walk keeps
the typed dictionary in wire order and shares it across the group's data
pages. A second dictionary or a PLAIN fallback frame yields a typed refusal.
[Snappy PLAIN V2 profile](parquet-list-required-container-v2-snappy-multi.md) · [Nullable LIST dictionary V2 profile](parquet-list-snappy-dictionary-v2.md)

The stored-body checker verifies a present CRC against the original payload
before expanding a dictionary, preparing a flag-selected data suffix, or
interpreting a level or index stream. An absent CRC uses the same
verify-if-present policy. The dictionary has exactly the advertised number
of signed little-endian INT32 words. For data, the raw repetition and
definition spans carry the original header extents. A false compression
flag uses the original index suffix and a true or omitted flag decodes
one exact Snappy member. The exact width-prefixed Hybrid stream yields one
in-range dictionary index per definition-two slot. A zero-value data page
still consumes its width octet.

Each nonempty V2 page starts at repetition zero. Header slot totals agree
with column metadata, row starts with footer group rows, and zero-value
slots with the decoded nested group. Definition zero is an empty present
list and definition one is a null child. The original page ordinals include
the dictionary at frame zero. Body and stitch failures retain original
coordinates and all earlier completed groups before IPC admission.

Dictionary entries, stored and expanded page bodies, levels, indices,
group slots and rows, and total file expansion are bounded. The file
budget includes dictionary bodies. Successful native V5 IPC preserves the
original field names, required parent validity, signed child order, and
exact EOS.
[Pinned V2 header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L788)

## Independent verification

PyArrow 26.0.1 produces two native files, with and without stored CRCs.
Each group has one original dictionary and five data frames, including a
zero-slot page. The files exercise both suffix flags, dictionary widths
zero through two, repeated indices, and both signed endpoints. Compact
Thrift, zlib, Hybrid decoding and PyArrow Snappy verify the exact original
extents, separate counts, index bytes, and resolved words. PyArrow reads
Lean's IPC through exact EOS.

An assembled positive control omits the compressed page's flag. The labeled
controls exercise stored CRC errors in the leading dictionary and raw
levels or index suffixes, a missing width, an out-of-range index, count
mismatches and a late continuation. The fallback control inserts a genuine
PyArrow PLAIN page into the dictionary chunk. PyArrow reads the assembled
rows while the strict profile returns the PLAIN frame's original error.
All late controls retain the first batch with a zero IPC row cap.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Hashes and observations](../../scripts/parquet-list-required-container-v2-dictionary/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-required-container-v2-dictionary/Oracle.py "$replay" |
  diff -u scripts/parquet-list-required-container-v2-dictionary/observations.txt -
```
