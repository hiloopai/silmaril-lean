# Checked native recursive Arrow IPC V5 streams

`Arrow.RecursiveSchema.Stream.readTrace` checks the original modern
[recursive Schema](arrow-recursive-schema.md) once. It reads successive
original frames with the shared [layout planner](arrow-recursive-batch.md)
and [logical row projection](arrow-recursive-rows.md). Each completed batch
carries its zero-based ordinal, absolute prefix offset, metadata size,
body length, and exact row count. Empty batches and positive row counts
at zero width survive as separate batches.
[Arrow 26.0.1 IPC streaming format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-streaming-format)

An invalid schema returns its original open error. A successfully opened
stream returns all complete batches before its terminal outcome. A
failure records the original reached envelope, batch, or row cause at
the original ordinal and byte cursor. The strict `read` entry point
returns success only when the modern eight-byte EOS ends the carrier
exactly. A missing marker is a framing error and bytes after a real
marker give a trailing-bytes error. A legacy prefix retains its
unsupported-framing cause.

The batch cap counts completed RecordBatches, including empty ones.
Envelope inspection still runs at the cap, so exact EOS succeeds there.
The first further admitted record envelope produces the batch-limit
error before opening its metadata. The inherited metadata, body, depth,
field, per-batch row, and physical slot limits apply. The collector is
bounded by the batch cap and those per-batch limits. After the schema
opens, each record uses its already checked envelope and the retained
carrier. `Batch.readFrame_of_envelope` proves agreement with the
standalone batch entry point, including its original typed errors.

`readTrace_wire` binds the opened schema and each completed batch to
the original bytes and proves the consecutive cursor chain. The chain
carries the checked layout, logical rows, and terminal result of the
first reached failure. `readTrace_failure` also identifies the failing
ordinal as the length of the completed prefix. `readTrace_eos` relates
success to the original continuation and zero length words at the exact
end. `read_iff` characterizes strict success.

The trace retains the full recursive field declarations, including
optional and repeated names in their original positions. An Arrow Events
adapter can use a positional signature keyed by the original recursive
fields and reify checked `RowFits` cells into `AlignedColumns`. That
typed conversion is a subsequent layer.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-stream-oracle/Axioms.lean
python3 scripts/arrow-recursive-stream-oracle/check.py
```

The pinned PyArrow oracle compares nine native batches across six
admitted streams, including a schema-only stream and the width-zero
sequence of 2, 0, and 1 rows. It independently checks each original
cursor, row count, positional value and EOS. A seventh genuine stream
checks legacy framing refusal. Eight labeled edits cover late semantic,
layout and framing failures, missing EOS, trailing bytes, and schema
open failure. Limit controls check the exact batch boundary and the
precedence of a reached malformed envelope.
[Fixture pins](../../scripts/arrow-recursive-stream-oracle/fixtures.json)
