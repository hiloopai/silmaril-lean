# Checked recursive Parquet signed V1 chunks

`Parquet.RecursiveSchema.Chunk.read` reads one original physical column
from its [checked chunk binding](parquet-recursive-schema.md). A
successful observation keeps the original page boundaries and first row
coordinates. Its `rows` projection gives one slot per footer row in
wire order. Each slot reports either the original absent ancestor or
leaf, or the signed INT32 or INT64 value.
[Parquet data page and nested encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding)

The admitted profile uses uncompressed PLAIN Data Page V1 with RLE
level header tags and zero repetition. The original compiled
definition width determines the value-body split. An all-required path
has no level section, so the complete body is the signed word sequence.
Other paths use the bounded V1 length prefix and the shared RLE/bit-packed
hybrid decoder. Its entire declared section must be consumed, subject
to the existing final packed-run padding rule. Each present slot
consumes one signed little-endian word, and the PLAIN reader must consume
the exact remaining bytes.

The checked binding supplies the original path, codec and span. The
reader checks the chunk byte and row budgets and the footer's total
uncompressed size before reading headers. It advances with the common
page reader over consecutive frames, checks both advertised page sizes
and verifies any stored CRC-32 against the original body. It refuses
other page kinds and value or level encodings. A page's count must fit
the remaining rows before its body is decoded. Reaching the exact chunk
end checks the total footer row count. A framing or page error retains
the original group, column, path, page ordinal, header byte and first
group-relative row. A definition-level refusal also carries the exact
row where the original level failed classification.

The `read_wire` law composes the original frame chain and total row
count with each page's bounded exact source slice and definition
witness. The PAGE V1 payload proof identifies the complete original
level region, ordered classification, and original signed words and
their assignment to present slots. Sibling consistency, nested row
assembly and recursive Arrow IPC emission are the follow-up layer.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-chunk-oracle/Axioms.lean
python3 scripts/parquet-recursive-chunk-oracle/check.py
```

Pinned PyArrow, Thrift and independent raw inspection check the two
populated predecessor files and the schema-only case, plus two genuine
multi-page files with and without checksums. The oracle compares 36
native Lean chunks and 84 page regions against original slot order,
signed endpoints, and PyArrow's nested values. A genuine V2 control and
twelve labeled edits exercise the first reached error coordinates,
including late definition, signed extent, checksum and frame failures.
Nineteen typed refusals also cover the bounded reader limits and
footer row total.
[Fixture pins](../../scripts/parquet-recursive-chunk-oracle/fixtures.json)
