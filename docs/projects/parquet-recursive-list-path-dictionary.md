# UNCOMPRESSED dictionaries for canonical signed LIST paths

ListPath reads one signed INT32 or INT64 leaf under a bounded canonical
LIST chain. An unindexed dictionary column uses codec zero and one
leading PLAIN dictionary. Each subsequent V1 or V2 data page uses the
local dictionary through RLE_DICTIONARY or carries PLAIN signed words.
The existing PLAIN codec profiles remain available per row group,
including in a file with dictionary groups. Legacy dictionary tags,
indexes, pageless groups and multi-leaf shapes remain outside this profile.
[PLAIN codec profiles](parquet-recursive-list-path-codecs.md) · [Compressed dictionaries](parquet-recursive-list-path-dictionary-codecs.md)

The leading frame starts at the original dictionary offset, consumes
one physical page from the frame budget, and advances to the original
first data offset without consuming a row or slot. The shared placement
and entry checks bind the dictionary to its original header, optional
stored-body CRC, and exact signed entries. Independent entry and byte
limits bound that read. Both footer totals include the original
serialized headers and payloads, including the dictionary.

The same level and live-ancestry checks apply to both data encodings.
Exactly one local index is resolved per terminal-definition slot.
The width-prefixed Hybrid suffix has independent byte and index bounds
and must be consumed exactly, with the permitted final packed padding.
V1 can carry an open row across a change of data encoding. V2 splits the
original raw level spans from the values, checks slot, row and null counts,
and closes the ancestry at both boundaries. V2 codec-zero suffixes use
the original stored bytes under either flag.

Dictionary and data-page refusals preserve the original group and
column path, physical ordinal, and absolute byte offset. Data refusals
also retain the incoming slot, row and ancestry cursor. Chunk framing
and total refusals retain the original column span. Events keep the
complete earlier groups under both projections. Empty selection validates the original bytes
and preserves each earlier group's row count. The strict Arrow IPC
bridge returns the native refusal and the selected prefix before target
budget admission. [Events](parquet-recursive-list-path-events.md) · [Arrow V5 IPC](parquet-recursive-list-path-to-ipc.md)

## Verification

Pinned PyArrow produces V1 and V2 sources at depths two, three and six
for both widths. The cases cover independent nullability, an empty
dictionary and genuine PLAIN fallback in both page versions and widths.
The oracle checks 38 dictionaries, 164 data pages and 40 Lean IPC
streams from 20 accepted files, including a Snappy admission case.
It independently inspects original Compact frames, CRCs,
signed dictionary entries, counted Hybrid levels and indices, data
anchors and both totals. It compares depth-two rows and slots with
TwoList and reads Lean IPC under full and empty selections through exact
EOS. Labeled reframes exercise both data encodings across V1
continuations and a row-aligned V2 transition. A labeled mixed-codec
file copies an original Snappy PLAIN group and an original UNCOMPRESSED
dictionary group.

Twenty-three typed controls cover dictionary placement, original
offsets, dictionary CRC and entry count, the physical page cap, exact
index consumption, both mixed-version boundary directions and separate
footer totals. Late dictionary and data errors are checked under both
projections, including exhausted IPC budgets.
[Fixture and producer pins](../../scripts/parquet-recursive-list-path-dictionary-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-dictionary-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-dictionary-oracle/check.py
~~~
