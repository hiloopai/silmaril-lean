# Opt-in Snappy V2 dictionary fallback for Parquet LIST

`ListFile.Multi.Snappy.DictionaryFallbackV2.convert` reads the established
canonical nullable LIST of nullable signed INT32 from a checked local Snappy
column chunk. Each group has a leading PLAIN dictionary, one or more
RLE_DICTIONARY Data Page V2 frames, then one or more PLAIN Data Page V2 frames.
Dictionary reentry fails at its original frame. The Parquet encoding spec
describes fallback to PLAIN when a dictionary grows too large. The single
switch and the requirement for both runs define this opt-in profile.
[Parquet dictionary encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8)

The checked footer, canonical LIST path and chunk reader bind the original
dictionary and first data offsets. Each data reader verifies any stored CRC
against the selected immutable frame before splitting the V2 body and
expanding the suffix, including the V2 raw suffix case. The original
repetition and definition spans are separate. V2 pages start at a row
boundary, and each page checks its slot, row and null counts. The group
carries the live LIST state and the remaining budgets across the encoding
switch. Dictionary bytes count against the file expansion cap. The separate
V1, dictionary-only V2, PLAIN V2 and default entry points keep their
existing admission rules.
[Dictionary V2 wire contract](parquet-list-snappy-dictionary-v2.md) · [PLAIN V2 wire contract](parquet-list-snappy-v2.md)

## Proofs and failure order

`readFrames_wire` proves a decomposition of the original frames with matching
indexed and PLAIN event lists. The indexed witness includes exact in-range
lookup from the signed dictionary. The PLAIN witness includes exact scalar
bytes and signed slot order. `readGroup_wire` binds the same source, group and
chunk, proves reconstruction from the ordered events, and accounts for the
remaining expansion budget. `readGroup_counts` sums the original V2 headers to
the footer slot and row totals and the reconstructed null-slot count.
`convert_readback` ties these witnesses to the field descriptor and one
ordered native Arrow LIST batch per row group through exact EOS.

Whole-chunk framing and offset checks precede body reads as in the
dictionary-only profiles. After dictionary admission, body failures are
reported in the original page order. The dictionary prefix is validated
before a missing suffix can fail. The suffix rejects reentry when it reaches
that frame. `convert_first_error` retains completed group batches with the
original indexed error and returns no byte carrier, even if the IPC writer
would also decline the input.

## Independent fixtures

PyArrow 26.0.1 writes the pinned two-group file with stored checksums. Each
group has a five-page indexed run and a three-page PLAIN run, including one
raw and two compressed PLAIN suffixes. Thrift Compact traversal checks the
footer, ordered raw tags and level extents. A byte-level comparator checks
the CRC, counters and scalar order independently. PyArrow reads both the
Parquet input and Lean's V5 Arrow output. The fixture includes INT32 endpoints,
repeated indices, null lists, empty lists and null children.

The negative files are labeled mutations or assembled controls. They cover a
retagged reentry, a missing indexed prefix, a stored PLAIN suffix CRC mismatch,
an earlier indexed CRC mismatch competing with late reentry, and a wrong V2
row count. The Lean controls also check missing PLAIN suffix, exact cumulative
budget and existing entry-point refusal.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Exact hashes and observations](../../scripts/parquet-list-snappy-dictionary-fallback-v2/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-snappy-dictionary-fallback-v2/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-dictionary-fallback-v2/observations.txt -
```
