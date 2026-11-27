# Opt-in selected GZIP PLAIN V1 Parquet DATE

`Date.Leaf.Gzip.readAll` and `Date.Leaf.Gzip.toIpc` select one flat required
or optional INT32 DATE leaf by zero-based physical ordinal. The strict
selected-leaf binding checks the original path and raw DATE annotation.
This profile admits codec 2 (GZIP) and PLAIN data page V1 with RLE level
tags. Each stored page body is one complete RFC 1952 member. GZIP uses
the existing Parquet payload and scalar page decoders. The profile
admits the same selected schema, name and nullability as the strict
DATE reader.
[Parquet compression, pinned at 2.14.0](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md)
· [RFC 1952](https://www.rfc-editor.org/rfc/rfc1952)
· [Selected DATE binding](parquet-date-selected-leaf.md)

The plan checks the original selected chunk extent, first data offset
and footer row count. The stored chunk span and sum of advertised
expanded page sizes have independent caps. Per-page stored bytes,
expanded bytes, level counts and GZIP controller calls are also bounded.
The outer Parquet CRC is optional and verified over the stored member
when present. The inner GZIP checksum and exact declared expanded length
are checked by the member decoder. V1 expansion covers the full
body, including any definition-level section. Dictionary offsets and
V2 page headers are typed refusals in this opt-in profile.
[Executable profile](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Defs.lean)

`pageWire_exact` identifies the original stored slice, CRC status,
independent byte bounds, exact single-member expansion, level mask
and ordered signed PLAIN words. The group laws bind those pages to
the original footer index and establish their exact nullable slot total.
`toIpc_readback` recovers the field descriptor and one complete ordered
Date32 batch per original footer group through exact EOS. The first-error
laws retain the earlier complete event batches and report the original
group, page, offset and cause before writer checks.
[Public contracts](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Thms.lean)

## Independent checks

PyArrow 26.0.1 emits two genuine multi-column GZIP PLAIN V1 files. DATE
is physical column one beside an unannotated INT32. The optional file
has stored CRCs, and the required file omits them. Each file has two
groups with three DATE pages per group. The signed slots include both
Int32 endpoints, pre-epoch dates and optional nulls. Apache Thrift 0.25.0
reads original frames and annotations. zlib checks the stored CRCs,
exact GZIP member consumption and inner trailers, and PyArrow reads the
actual Lean-emitted IPC. The fixture also exercises the inclusive
stored and expanded chunk caps.
[Pinned Arrow source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture hashes and observations](../../scripts/parquet-date-gzip-v1-oracle/fixtures.json)

Two separately labeled malformed mutations reject a late outer CRC and
a late inner GZIP CRC with a recomputed valid outer CRC. PyArrow reads
the complete preceding group and rejects both damaged groups. Lean
retains that group and the original indexed error with a zero IPC batch
cap. Other controls use genuine inputs with independently lowered
stored, expanded or GZIP call budgets, and genuine out-of-profile GZIP
V2 and dictionary chunks. The strict PLAIN profile rejects the
GZIP files at its original codec check.
[Oracle](../../scripts/parquet-date-gzip-v1-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-v1/Axioms.lean
python3 -I scripts/parquet-date-gzip-v1-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
