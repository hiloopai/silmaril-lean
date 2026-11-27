# Opt-in selected Parquet DATE dictionaries

`Date.Leaf.Dictionary.readAll` and `Date.Leaf.Dictionary.toIpc` select
one DATE leaf by zero-based physical column ordinal. They use the
strict selected-leaf binding, so the raw DATE annotation, flat path and
required or optional INT32 type all refer to the original snapshot.
The existing DATE annotation rules admit modern DATE alone, modern
DATE with matching converted DATE (6), or converted-only DATE when
the modern annotation is absent.
[Selected DATE binding and profile](parquet-date-selected-leaf.md)
· [Parquet 2.14.0 DATE](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)

Each selected chunk must contain one leading PLAIN (0) dictionary and
V1 or V2 data pages using RLE_DICTIONARY (8). The reader checks the original
dictionary and first data offsets, the in-file chunk span and disjointness
from other chunks, and the declared row total. The shared INT32 framer
checks the bounds for frames, dictionary entries and page bodies. The
shared scalar and dictionary-index decoders check definition levels, exact
consumption of the width-prefixed hybrid index stream, and lookup into
the chunk-local signed dictionary. This profile rejects compression,
CRC-bearing pages, legacy PLAIN_DICTIONARY tags and PLAIN data fallback.
The strict PLAIN and one-column page-less entry points continue to use
their existing admission profiles.
[Parquet 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)
· [Dictionary framer](../../Silmaril/Formats/Parquet/DictionaryChunk/Defs.lean)
· [DATE entry points](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Defs.lean)

`readGroup_exact` relates one group read to its original selected chunk,
the original bounded frame chain, the signed PLAIN entries and the
concatenation of typed data-page slots. `pageWire_exact` exposes the
original payload's validity mask and ordered in-range lookups.
`toIpc_readback` recovers the exact field name and nullability, one batch
per original group in footer order, and the ordered nullable signed days.
The first-error laws preserve the exact earlier complete event batches
and report the original footer index and cause. A source failure takes
precedence over the IPC writer limits and yields no completed IPC bytes.
[Public theorem header](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Thms.lean)

## Independent checks

PyArrow 26.0.1 produces V1 and V2 dictionary files with the optional DATE
leaf at physical ordinal 1, next to an unannotated INT32. Each file has
three groups with separate dictionaries, repeated dates, nulls, negative
days and both signed Int32 endpoints. Apache Thrift 0.25.0 independently
reads the original footer and page headers. The oracle checks absolute
frame offsets, PLAIN words, packed validity bits and index words, and
uses PyArrow to read the emitted Date32 IPC. It observes the endpoints
as signed day words, which also permits values outside the host calendar
object range.
[Arrow 26.0.1 source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture observations](../../scripts/parquet-date-dictionary-oracle/fixtures.json)

A Thrift-located one-octet edit changes the first reference of the last
group to absent index 3. PyArrow independently rejects the last group,
and the Lean check observes both earlier groups plus the exact group
index, page index and original frame offset. Further controls cover
PLAIN fallback, a missing dictionary, compression, CRC, entry budget and an adjacent
unannotated ordinal. The strict PLAIN reader rejects both dictionary
files.
[Oracle](../../scripts/parquet-date-dictionary-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Thms +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-dictionary/Axioms.lean
python3 -I scripts/parquet-date-dictionary-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
