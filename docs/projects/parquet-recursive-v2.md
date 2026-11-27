# Checked recursive signed Parquet V2

The original recursive chunk walk admits UNCOMPRESSED PLAIN Data Page
V2 with signed INT32/INT64, required and optional Structs and the
canonical three-level LIST schema. Each physical leaf has at most one
repeated ancestor. The existing chunk binding requires codec
UNCOMPRESSED and PLAIN/RLE encodings. It refuses dictionary pages,
offset indexes and column indexes.

The header stores the raw repetition and definition section lengths.
The reader uses the original absolute V2 spans in the order repetition,
definition and values. A zero maximum requires an omitted section.
Each other section must decode exactly the advertised slot count
with the bounded hybrid reader. The signed value suffix must have
exactly one full-width word per present slot. An optional CRC32 is
checked on the original stored body. With codec UNCOMPRESSED the
resolved V2 compression flag selects the identity codec, including
when the flag is omitted and defaults to true. The stored and
uncompressed sizes must be equal.

`num_values` counts level entries. `num_rows` counts repetition-zero
starts. `num_nulls` counts entries without a signed value, including
null and empty List markers, null elements and absent ancestors.
Every nonempty V2 page begins at repetition level zero, including in
an unindexed chunk. V2 leaves the next page at a closed row boundary.
The shared walk also accepts a V1/V2 transition at a row boundary. The
existing V1 path retains live continuation across admitted V1 cuts.
The writers emit V1.
[Pinned Parquet V2 specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L779)

`decodeV2Page_wire` binds the original header, checksum, exact three
source slices, raw level runs and shared classified signed slots.
`V2PageWire.accounting` gives the original count and signed suffix
extent equations and the closed boundary. The combined chunk wire law
retains the original page and slot order and attains the footer slot
and row totals. The existing row-group, direct Events and native IPC
routes use the same witnesses. Errors retain the original group,
column, page and cursor.

## Fixtures and regressions

Pinned PyArrow yields genuine nested V2 rows in multiple groups,
checksummed pages, null and empty Lists, null elements, signed
endpoints and unequal sibling page cuts. Its genuine zero-row group
contains pageless chunks and hits the existing footer interval
refusal. A separately labeled assembly gives that group one valid
V2 frame per leaf with matching metadata. PyArrow and Lean read all
three groups, including the zero-row group.

Independent Thrift and level inspection matched 40 chunks and 98
pages, including a labeled V1/V2 transition and a V2 header with an
omitted compression flag. Six actual Lean IPC streams preserve the
ordered native rows and exact EOS. Seventeen typed controls include
late count and CRC failures, malformed framing and lengths, excess
level and value data, a V2 page starting mid-row and a V1 continuation
after a V2 page. Direct Events retains the complete group prefix and
original late error. Native IPC returns that same source error ahead
of output limits.

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-v2-oracle/Axioms.lean
python3 scripts/parquet-recursive-v2-oracle/check.py
```
