# Compressed dictionaries for canonical signed LIST paths

The unindexed signed INT32 and INT64 ListPath dictionary reader accepts
UNCOMPRESSED (0), Snappy (1), single-member GZIP (2), bounded
single-frame dictionary-free Zstandard (6), and LZ4_RAW (7). Each
original column chunk selects its own codec. The PLAIN dictionary page
uses that codec for its entire body. Data pages use RLE_DICTIONARY
or PLAIN and retain the same bounded codec profile and per-page checks
as the existing ListPath reader. Deprecated LZ4, legacy PLAIN_DICTIONARY
tags, and raw Brotli are outside this admission profile.
[PLAIN codecs](parquet-recursive-list-path-codecs.md) · [Dictionary encoding](parquet-recursive-list-path-dictionary.md)

The leading dictionary starts at the original dictionary offset and its
payload end equals the original first data offset. The reader preserves
the serialized header spans and checks optional CRC on the stored bytes
before expansion. Independent dictionary entry, stored byte and decoded
byte caps apply. The checked decoded body consists of exactly the
advertised signed words. The dictionary and data frames contribute their
original serialized headers to both footer totals, with stored bodies
in the compressed total and decoded extents in the uncompressed total.

V1 expands the entire data body. Its section coordinates refer to that
decoded body for compressed columns. V2 checks the original raw Hybrid
level spans and dispatches only a flagged value suffix. A false flag
uses the original suffix without codec work. Each indexed page consumes
an exact counted Hybrid stream against its own chunk's checked table.
V1 carries live ancestry across encoding changes. V2 independently
accounts for rows, slots and nulls and closes both boundaries.

The original typed error and coordinates carry through Events and
strict IPC conversion under both selections. Empty selection checks
the same source and preserves completed row-group counts. Source
refusals take precedence over IPC output budget failures.
[Events](parquet-recursive-list-path-events.md) · [Arrow V5 IPC](parquet-recursive-list-path-to-ipc.md)

## Verification

Pinned PyArrow produces genuine V1 and V2 sources for each codec and
signed width at LIST depths two, three and six. Independent Compact,
Hybrid and signed-word inspection uses reference Snappy, liblz4, zlib
and libzstd to check the original stored payloads, CRCs, decoded
extents and footer totals. The oracle checks 55 accepted inputs, 113
dictionaries, 678 data frames and 110 Lean IPC streams. There are 217
PLAIN fallback pages, with genuine fallback in both versions. It compares depth-two rows and slots with TwoList and
reads Lean IPC under full and empty projection through exact EOS.

Labeled controls include raw V2 index bypasses for each codec and a
Snappy reframe with V1 continuations and a V2 transition. The mixed-codec
fixture copies original frames into five groups. A late index exists in
an earlier group's table and fails against its own. Twenty-five typed
controls also exercise independent stored and decoded limits, CRC before decompression
and the data anchor, codec work caps, trailing input, wrong extent,
legacy tags and independent footer totals.
[Producer, reference and fixture pins](../../scripts/parquet-recursive-list-path-dictionary-codecs-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-dictionary-codecs-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-dictionary-codecs-oracle/check.py
~~~
