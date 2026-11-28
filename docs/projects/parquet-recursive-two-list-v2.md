# Checked V2 data pages beneath two canonical LISTs

The TwoList reader accepts unindexed UNCOMPRESSED PLAIN Data Page V1
and V2 for one signed INT32 or INT64 leaf under two canonical LISTs.
The checked thresholds for the outer list, inner element and leaf
still govern the definitions and the legal repetitions. The same
logical Rows, Events and native Arrow IPC entry points consume the
checked observations. This profile describes the identity codec.
[Bounded Snappy extension](parquet-recursive-two-list-snappy.md)
[Schema and V1 cursor](parquet-recursive-two-list.md) · [Arrow IPC](parquet-recursive-two-list-to-ipc.md)

V2 binds the parsed original Compact header and stored body. The body
CRC is checked when present. The original header byte lengths split the
body into consecutive unprefixed repetition and definition slices and the
signed PLAIN suffix. The bounded counted Hybrid decoders consume the raw
level slices exactly. Both values of the compression flag resolve to
identity under codec zero. The default for an omitted flag is true and
the stored and decoded page sizes must agree.
[Parquet DataPageHeaderV2](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

The decoded level and aligned word counts equal `num_values`. A
repetition-zero slot counts once toward `num_rows`. Any slot whose
definition does not reach the leaf contributes to `num_nulls`, including
null and empty LIST sites. The signed suffix contains exactly
`num_values - num_nulls` words of the original width and order.
The chunk counts both serialized header and payload bytes in both
original footer totals. Its ordered frame walk starts at the data-page
offset and ends at the declared column end.

V1 carries live ancestry across pages. A nonempty V2 page must start at
repetition zero and starts with closed ancestry even after a V1 page.
V2 also closes its outgoing cursor, so the following data page cannot
continue its final row. The cursor enforces both depths independently
within a page. Direct Events retains every earlier complete group
under both top-level selections and reports the first failed group.
A decoding error retains its original page ordinal, byte offset and
incoming cursor. A framing error retains its original chunk span.
The original source failure takes precedence over IPC output limits.

## Reproduction

The pinned oracle checks genuine PyArrow V2 output for every combination
of outer, inner and leaf nullability at both signed widths. Each file
contains two groups with multiple pages. Independent Compact, Hybrid, CRC
and signed-word inspection compares every page header, raw span, slot
and cursor against Lean. Authored reframings check consecutive V1 starts
at repetitions one and two, V1-to-V2 and V2-to-V1 boundaries, and explicit
and default true identity flags. PyArrow reads each native Lean IPC
stream with the original nested declarations and rows or zero projected
columns, and independent framing checks the exact EOS.

Typed controls cover both invalid mixed-boundary directions at each
repetition depth, row, null and slot counts, section and suffix extents,
CRC, footer totals and offset, page cap and body cap. Late row, null, CRC
and suffix failures retain the complete first group through empty
projection and take precedence over an exhausted IPC budget.
[Producer, source and IPC pins](../../scripts/parquet-recursive-two-list-v2-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-v2-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-v2-oracle/check.py
~~~
