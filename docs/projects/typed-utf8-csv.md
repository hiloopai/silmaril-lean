# Typed nullable CSV over UTF-8 wire bytes

Import `Silmaril.Formats.Csv.Typed.Utf8.Defs` for `encode`, `decode`, and the
`string` cell codec. The entry points take the same ordered `Typed.Schema`,
dependent family of `Typed.CellCodec`s, and nullable `Typed.Table` as the
strict ASCII API. For a signed Int32 column use `Typed.Codecs.int32` from
`Silmaril.Formats.Csv.Typed.Codecs.Defs`. [Typed schema and tagging](typed-csv.md)
· [UTF-8 CSV wire profile and RFC citations](utf8-csv.md)

The first record must match the supplied header bytes in schema order. Each
body record must have the declared width. A cell spelled `N` denotes null.
A leading `T` denotes a present value, and the bytes following it go to the
column codec. For a string column, `T` means present empty text, `TN` means
the literal string `N`, and `TT` means the literal string `T`. A missing
column fails the width check. An untagged empty field fails the tag check.
A zero-column schema uses one empty field as its header and as each body row,
so the physical record count is one greater than the typed row count.

The string cell codec always prints the original UTF-8 bytes of a Lean string.
It parses well-formed UTF-8 to a string without normalization. CSV wire
representability is checked separately over the complete header and tagged
fields. For example, a tab or NUL can be printed and parsed by the string
codec, but a table containing it produces `unrepresentableWire`. Quotes,
commas, CR and LF are carried by CSV quoting. The input wire decoder reports
`malformedWire` for either malformed UTF-8 or CSV outside the admitted grammar.
Once lexical decoding succeeds, typed header, width, tag and parse errors
retain their existing meanings. The Int32 codec accepts canonical decimal in
the range −2147483648 through 2147483647. [Int32 and strict ASCII cell codecs](../../Silmaril/Formats/Csv/Typed/Codecs/Thms.lean)

## Laws

`string_parsePrint` and `string_printParse` give exact string and text-byte
inverses. Together with the corresponding Int32 laws, they discharge the
cell-codec assumptions of `decode_encode` and `encode_of_decode`.
`decode_encode` recovers the exact ordered typed table after successful
encoding, including nulls and row count. `encode_of_decode` recovers the
exact lexical rows after successful decoding, with canonical wire quoting
and CRLF. These claims apply to successful operations under the supplied
schema. The ASCII compatibility laws `decode_eq_ascii` and `encode_eq_ascii`
compare both APIs with identical cell codecs on ASCII input and ASCII
lexical exports respectively. [Typed UTF-8 theorems](../../Silmaril/Formats/Csv/Typed/Utf8/Thms.lean)

The boundary accepts a typed table supplied by its caller. Named-table
projection and Arrow or Parquet byte interpretation are separate steps.

## Verification

The independent harness uses CPython 3.13.5 with strict UTF-8,
`newline=""`, comma, doubled quotes, and a `QUOTE_ALL` CRLF writer.
It checks the reader's lexical rows, compares Lean's typed observations
with fixed values, and compares canonical writer bytes in both directions.
It also checks exact typed errors for malformed and structurally invalid files.
[Fixture hashes](../../scripts/typed-utf8-csv-oracle/fixtures.json)
· [Pinned CPython source](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/Modules/_csv.c)

```sh
lake build --wfail +Silmaril.Formats.Csv.Typed.Utf8.Thms +Silmaril.Formats.Csv.Typed.Utf8.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Csv.Typed.Utf8.Thms +Silmaril.Formats.Csv.Typed.Utf8.Tests'
python3 -I scripts/typed-utf8-csv-oracle/check.py
```

## Opt-in row-budgeted decoding

[`Typed.Utf8.Bounded.decode`](../../Silmaril/Formats/Csv/Typed/Utf8/Bounded/Defs.lean)
uses the same UTF-8 field parser, exact ordered header, cell codecs,
nullable tags, and zero-column marker as the complete typed decoder. It
parses the header once and checks the remaining data-row budget before
reading each nonempty body suffix. Each accepted marker at width zero
costs one row. A header-only wire can complete with budget zero.

The reader parses and validates one logical record at a time, including
quoted newlines. It does not build a whole table of raw records. The
budget bounds the accepted typed rows retained while decoding. Parsing
can still allocate the header, the current record, and its fields. The
wire is already supplied as a byte list. The row budget is not a bound
on input size, field width, work, or total allocation.

An empty suffix completes after a valid final record, with or without
its final CRLF. A nonempty body suffix at a depleted budget instead
returns `.rowLimit` before inspecting another record. Header failures
precede body processing. Within the budget, the first reached malformed
record or typed cell returns its CSV error. This can differ from the
complete decoder, which lexes the entire wire before typed validation.

`Bounded.decode_ok_iff` proves that success returns exactly the complete
decoder's ordered table within the cap, with no partial result on error.
The complete decoder and its existing named import keep their API and
behavior.

The CPython 3.14.7 oracle writes quoted multiline text, present-empty
and null cells, width-zero markers, bare blank records, and late
malformed cases. Lean checks exact and zero budgets and verifies the
difference between reaching a bad record and stopping before it.

```sh
lake build --wfail +Silmaril.Formats.Csv.Typed.Utf8.Bounded.Checks
python -I scripts/csv-row-budget-oracle/Generate.py /tmp/csv-row-budget
lake env lean --run Silmaril/Formats/Csv/Typed/Utf8/Bounded/Checks.lean /tmp/csv-row-budget
```
