# Opt-in Snappy dictionary V1 Parquet LIST to native Arrow IPC

`Parquet.ListFile.Multi.Snappy.DictionaryV1.convert` reads the canonical
nullable LIST of nullable signed INT32 children. It requires codec one
and exactly one leading PLAIN dictionary followed by one or more
RLE_DICTIONARY Data Page V1 frames. The checked footer selects the original
local chunk and its schema path, physical column ordinal, and row group.
Both the dictionary offset and the first data page offset must match the
original frame chain. This profile admits dictionary header encoding
zero and data encoding eight. PLAIN fallback, deprecated
PLAIN_DICTIONARY, V2 dictionary data, and other nested shapes are outside
the profile.
[Pinned dictionary encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8) · [Original canonical LIST profile](parquet-list-file.md)

Each frame's optional CRC is verified over its original stored body.
A present checksum must match before decompression. The expanded
dictionary has exactly four bytes per declared entry, decoded as signed
little-endian INT32 in wire order. Entry and dictionary byte limits
apply before expansion or decoding. For each data page one exact Snappy
member expands the full V1 body, including the original length-prefixed
RLE Hybrid repetition and definition streams. The checked definition
mask supplies the present-value count. The untouched suffix supplies
one width byte and exactly that many bounded Hybrid indices, each
resolved in the same chunk-local dictionary. A page with zero present
values still supplies the width byte and an empty run suffix.
[CRC contract](parquet-page-crc32.md) · [V1 LIST slot and row semantics](parquet-list-v1.md)

The stateful walk retains null lists, empty lists, null children, and
repeated signed values in original order. The dictionary consumes expansion
budget but contributes zero data slots or rows. Each data page contributes
its original advertised slot count, including structural markers, and a
zero-slot page contributes no rows. The full data slot and row totals must
match their separate footer counts. A V1 page can continue the live list
under the existing continuation rule, with a new row required at the
group boundary and when an OffsetIndex is advertised. The file-wide
allowance includes expanded dictionary and data bodies.
[Continuation rules](parquet-list-continuation.md)

`selectChunk_wire` ties the original offsets to the selected group.
`readEntries_wire` proves signed dictionary order and
`readValues_wire` proves exact suffix consumption and in-range lookups in
original index order. `readGroup_wire` uses those witnesses at the exact
original data pages and reconstructs the checked ordered group rows.
`convert_readback` ties those rows and the footer schema to native Arrow
IPC batches through exact EOS.

Complete chunk framing precedes the original body walk. A dictionary
failure carries original page ordinal zero and its absolute header
offset. A data failure carries the original data-page ordinal within
that frame chain. `convert_first_error` preserves completed earlier
groups and the original typed source error ahead of native IPC admission.
A source failure yields no IPC carrier.
[Public theorem headers](../../Silmaril/Formats/Parquet/ListFile/Multi/Snappy/DictionaryV1/Thms.lean)

## Independent reproduction

PyArrow 26.0.1 generates both native V1 inputs with multiple row groups and
five data pages per chunk. The checksummed input exercises both signed
INT32 endpoints, repeated dictionary indices, null lists, empty lists,
null children, and zero-slot data pages. The optional-checksum input adds
a group whose dictionary expands to zero entries. Thrift 0.25.0
independently checks exact original footer and frame extents. A separate
Hybrid walk and PyArrow's Snappy codec check ordered indices, dictionary
words, and reconstructed rows. zlib verifies the stored CRCs. PyArrow
also reads the native input and the Lean-written IPC.

The comparator distinguishes stored CRC mutations from assembled
controls. The controls cover late dictionary and data CRC failures, a
valid CRC over an out-of-range index, a wrong dictionary count, a PLAIN
fallback tag, a mismatched first data offset, and a one-byte-short file
expansion cap. Lean checks each typed refusal with the first batch
retained under a rejecting IPC row budget.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Exact hashes and observations](../../scripts/parquet-list-snappy-dictionary-v1/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Examples
python3 scripts/parquet-list-snappy-dictionary-v1/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-dictionary-v1/observations.txt -
```
