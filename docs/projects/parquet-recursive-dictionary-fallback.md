# PLAIN fallback in recursive signed Parquet dictionary chunks

The unindexed, UNCOMPRESSED recursive INT32/INT64 Struct/LIST
reader accepts PLAIN and RLE_DICTIONARY Data Pages V1 and V2 in
the same dictionary-first column chunk. The reader requires the
original leading PLAIN DictionaryPage and original first data-page
offset. Any later DictionaryPage is a typed failure, including
after a PLAIN page. PLAIN-only columns use the existing binding.
[Parquet column chunks and page metadata](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#column-chunks)

PyArrow 26.0.1 writes an RLE_DICTIONARY prefix and a PLAIN tail
when the dictionary crosses its size limit. The file format
specifies the encoding in each data page header and permits a
partly dictionary-encoded column chunk. Reader admission follows
the original tag on each page, with the same leading dictionary
available throughout the chunk. A PLAIN page consumes the exact
signed words for its present slots. An RLE_DICTIONARY page consumes
the exact Hybrid stream and resolves each present slot against
the same ordered dictionary. Unsupported tags retain their V1
or V2 errors.
[Parquet dictionary encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8)

The mixed-page wire relation carries the existing PLAIN and
dictionary witnesses through one original frame chain. It counts
the leading dictionary as a physical page with zero slots and
rows, and preserves the original footer spans and counts. V1
carries its live List state even when the encoding changes.
V2 requires a row start and closes the boundary for either
encoding. Rows and IPC use the same checked observations, and
direct Events retains the complete earlier groups and original
addressed failure through empty projection.

## Fixtures and regressions

Pinned PyArrow emits genuine V1 and V2 fallback under a 48-byte
dictionary size limit and two-row write batches. Both signed
widths exceed the limit. The genuine files also exercise nested
nulls, empty lists, signed endpoints, and separate PLAIN-only
and dictionary-only cases. Independent Compact, Hybrid and
signed-word inspection follows the original tags, frame spans,
stored CRC and words in the PLAIN suffixes. PyArrow reads the
Lean-emitted IPC streams, and independent framing checks exact EOS.

Authored V1 and V2 edits resolve selected original indices and
store the corresponding PLAIN words while retaining the original
levels and later dictionary pages. These files exercise a PLAIN
first data page and a return to RLE_DICTIONARY after PLAIN. Two
additional edits retain the existing mid-row V1 split with
different encodings on either side. Changing the preceding
PLAIN page to V2 rejects the later V1 continuation.

The negative controls include missing and repeated dictionaries,
conflicting original frame headers, unsupported encoding,
checksum corruption, and short or trailing PLAIN words. A late
PLAIN failure in either version preserves the earlier group
through empty projection and takes precedence over IPC writer
limits.
[Fixture pins](../../scripts/parquet-recursive-dictionary-fallback-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-fallback-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-fallback-oracle/check.py
~~~
