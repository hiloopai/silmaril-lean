# Checked dictionary data beneath two canonical LISTs

The two-LIST reader supports one signed INT32 or INT64 leaf in unindexed
Parquet V1/V2. The initial dictionary-first fixtures cover UNCOMPRESSED and
SNAPPY. Per-page PLAIN fallback and RLE_DICTIONARY may alternate in the
same chunk. The original data page header selects the page's decoder.

[Current dictionary codec matrix](parquet-recursive-two-list-dictionary-codecs.md)

The reader requires one leading PLAIN DictionaryPage for a
dictionary-first column. The original dictionary and first data
offsets identify consecutive frames in the checked chunk. Shared
dictionary handling checks the original stored CRC, byte and entry
caps, decoded extent, and exact signed words in wire order. The
dictionary occupies one physical page and consumes zero row/value slots.
Both footer totals include its original header and body.
[One-LIST dictionary and fallback](parquet-recursive-dictionary-fallback.md) · [Two-LIST codec table](parquet-recursive-two-list-codecs.md)

Each indexed page consumes its width octet and the entire counted
Hybrid stream for the present slots. Its exact witness retains the
original suffix and bounds each selected index against the same local
dictionary. The final packed run may include up to seven padding positions.
Only the specified index count produces lookups. Snappy V1 expands
the whole original stored body. Snappy V2 leaves the original levels
raw and expands only the value or index suffix under a true flag.
The index suffix uses the extent from the original header. The fixed
signed-word extent applies to PLAIN.

The two-LIST cursor carries its live ancestry across V1 pages and
encoding changes. V2 starts at repetition zero and closes its outgoing
cursor. Logical Rows, direct Events and native Arrow IPC use the
resulting signed slots. Direct Events preserves the complete prior
groups and original error address through empty projection. IPC
gives an addressed source failure precedence over its output limits.
[Two-LIST cursor](parquet-recursive-two-list.md) · [IPC readback](parquet-recursive-two-list-to-ipc.md)

## Reproduction

Pinned PyArrow produces both signed widths, both codecs, both page
versions, genuine dictionary-to-PLAIN fallback, and empty dictionaries.
Independent Compact, Hybrid, Snappy, signed-word and CRC inspection
checks the original frame order, offsets, entries, indices and totals.
The authored mixed chunk exercises V1 continuation at repetitions one
and two across encoding changes, V2 closure, and nonzero bytes in
ignored final Hybrid padding. An authored Snappy edit checks the raw
V2 index suffix. Native IPC readback reaches exact EOS for each
selection.

Typed controls cover missing, duplicate and late dictionaries,
wrong data offsets, dictionary CRC and word extent, entry and byte
caps, exact index stream and lookup, physical page count, both
continuation boundaries, and footer accounting. Late dictionary,
index and PLAIN failures exercise the completed-prefix contract.
[Producer, source and IPC pins](../../scripts/parquet-recursive-two-list-dictionary-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-dictionary-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-dictionary-oracle/check.py
~~~
