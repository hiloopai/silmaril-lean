# Native Parquet V2 for a canonical signed LIST path

The bounded ListPath reader accepts local, unindexed UNCOMPRESSED PLAIN
Data Page V2 for one signed INT32 or INT64 leaf under a canonical LIST
chain. The original footer still supplies the single column association,
the repetition and definition maxima, both header-inclusive sizes and
the independent row and slot counts. V1 and V2 can occur together in a
chunk. [Schema and trace core](parquet-recursive-list-path.md) · [Native V1 reader](parquet-recursive-list-path-v1.md)

V2 uses the shared repeated-leaf Compact framing, stored-body CRC
check, and bounded split of the original payload. Its header gives the
absolute raw Hybrid repetition and definition spans. The word suffix
is the original stored suffix for codec zero under either V2 flag,
including the default when the flag is omitted. The same signed
decoder and ancestry scan serve both versions. The V2 witness keeps the
original header, checksum, raw slices, exact Hybrid counts and signed
words. The shared V2 counter check verifies the number of repetition-zero
starts and the exact null marker count separately from the slot count.

## Complete-row boundaries

A V2 page starts a new row from a closed ancestry cursor and leaves
a closed cursor for the following page, including when it has zero
slots. Successive V1 pages can still continue any ancestor reached
by both adjacent slots. Across page versions, a new row can follow
either version. A V2 page beginning at a positive repetition or a
positive repetition in V1 immediately after V2 is refused with the
original page address.

Rows, Arrow Events and strict Arrow V5 IPC use the same checked group
observations. Full-field and empty projection preserve complete prior
groups and the first reached native failure. Column and offset indexes,
dictionary encoding and pageless groups are outside the profile.
The reader also supports bounded compressed columns. [Codec profiles](parquet-recursive-list-path-codecs.md) · [Events](parquet-recursive-list-path-events.md) · [Arrow V5 IPC](parquet-recursive-list-path-to-ipc.md)

## Verification

Pinned PyArrow and independent Compact, Hybrid, CRC and signed-word
inspection check 18 sources and 101 pages at depths 1, 2, 3, 4, 6 and
16 across both signed widths. The native V2 files have multiple pages
per populated group and cover required and optional ancestry, nested
nulls and empties, and absent CRC. Depth-two schema, groups and slot
observations agree with the existing TwoList reader.

Labeled mixed and flag edits preserve the observations of the genuine
V1 and V2 sources. The mixed file starts V1 continuations at repetitions
one, two and three and contains a physical zero-slot V2 page. Both
projections yield 36 native IPC streams through exact EOS. Nineteen
typed controls exercise both mixed boundary directions, counters,
level and signed-word extents, CRC, footer size, and profile refusals.
Late row, null, signed extent and CRC errors preserve the first complete
group under both selections and take precedence over IPC output limits.
[Producer and fixture pins](../../scripts/parquet-recursive-list-path-v2-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-v2-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-v2-oracle/check.py
~~~
