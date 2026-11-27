# Opt-in Snappy dictionary V2 Parquet LIST to native Arrow IPC

`Parquet.ListFile.Multi.Snappy.DictionaryV2.convert` accepts the canonical
nullable LIST of nullable signed INT32 children with one original PLAIN
dictionary and RLE_DICTIONARY Data Page V2 frames. The checked local
column selects Snappy. The shared dictionary walk verifies the original
dictionary and first data offsets and reads the exact signed PLAIN
dictionary in wire order. PLAIN fallback, legacy PLAIN_DICTIONARY tags,
and mixed data-page versions are outside this profile.
[Existing dictionary V1 contract](parquet-list-snappy-dictionary-v1.md) · [Pinned dictionary encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8)

The optional CRC covers the entire stored V2 payload, including both
raw level streams and its stored index bytes. After the original
frame passes CRC verification, the shared V2 preparation checks each
raw repetition and definition extent and their sum against both body
sizes. It resolves the index suffix as raw when `is_compressed` is
false or as one exact Snappy member when true. An omitted flag uses
the wire default of true. The absolute level spans remain tied to the
original stored frame. The per-page and cumulative expansion limits
include the raw levels and expanded index bytes as well as the
leading dictionary.
[Pinned V2 header and flag](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L742-L782) · [Shared V2 geometry](parquet-list-snappy-v2.md)

`readFrame_wire` establishes that the definition levels select exactly
`num_values - num_nulls` present values. Their width-prefixed Hybrid
indices are consumed exactly and select in-range signed dictionary
entries in original index order. A page with no present values
still carries its original bit-width byte and an empty run suffix.
The page's null-slot count includes null-list and empty-list markers
as well as null child slots.

Every nonempty V2 page starts at repetition zero. Repetition one
continues the current row within that page. The shared LIST state
keeps each completed row in order and handles a zero-slot page without
adding a row. The dictionary contributes no data slots or rows.
`readGroup_counts` proves that the V2 slot and repetition-zero totals
match their separate footer counts and that the V2 null totals agree
with the reconstructed null-slot count.

Chunk framing runs before body checks and retains its typed group
error. After framing, a failed dictionary carries page ordinal zero
and its original absolute header offset. A V2 data failure carries the
original page ordinal and offset, including after an admitted prefix.
`convert_first_error` preserves earlier complete groups and the
original typed cause ahead of IPC admission. An error yields no IPC
carrier. `convert_readback` relates the original checked groups to the
native Arrow names, nested nullable rows and exact EOS.
[Public theorem headers](../../Silmaril/Formats/Parquet/ListFile/Multi/Snappy/DictionaryV2/Thms.lean)

## Independent reproduction

PyArrow 26.0.1 produces two native inputs with five V2 data pages
per chunk and both suffix flags. A compressed suffix stores 68
expanded bytes in 12 bytes and represents 513 indices. The native
inputs exercise repeated indices, signed INT32 endpoints, null and
empty lists, null children, and zero-slot pages. The checksum-free
input adds a group with a zero-entry dictionary. A separately
assembled positive control removes a true flag and leaves its stored
payload and CRC intact.

Thrift 0.25.0 checks original footer and page extents. PyArrow's
Snappy codec, zlib, and a separate Hybrid walk check suffixes, CRCs
and signed dictionary lookups. PyArrow reads the native input, the
assembled omitted-flag control and the Lean-written IPC. Separate
mutated controls cover late CRC errors in the dictionary, raw levels
and compressed indices. Assembled refusals cover bad geometry,
a continuation at a V2 boundary, wrong row or null counts, an
out-of-range index with valid CRC, and a PLAIN tag. The failure
controls and the one-byte-short cumulative budget retain the first
batch under a rejecting IPC row budget.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Exact hashes and observations](../../scripts/parquet-list-snappy-dictionary-v2/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Examples
python3 scripts/parquet-list-snappy-dictionary-v2/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-dictionary-v2/observations.txt -
```
