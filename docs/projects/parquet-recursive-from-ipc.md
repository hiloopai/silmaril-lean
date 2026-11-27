# Recursive Arrow IPC to native Parquet

`Parquet.RecursiveSchema.Repeated.Writer.FromIpc.convert` takes a native
Arrow IPC byte carrier and returns complete Parquet bytes and their
checked footer. The common profile is the existing modern little-endian
V5 signed INT32/INT64, Struct and List stream reader and the existing
UNCOMPRESSED PLAIN Data Page V1 writer with canonical three-level LIST.
The Parquet declaration admits one repeated ancestor per physical leaf
and requires names and nonempty Structs and roots. Unsupported
declarations receive the original typed writer refusal.

## Source and writer admission

The bridge consumes the original source through an explicit modern EOS
at the exact end of the stream before consulting writer options or
budgets. `openError` carries the original schema-open cause.
`terminal` carries the original declaration, completed batch prefix
and first reached failure with its byte cursor, ordinal and typed cause.
These errors have no Parquet result.

After EOS, each batch supplies one ordered group with its original
explicit row count. An empty batch produces one zero-row group.
A schema-only stream produces zero groups. Writer options select the
existing CRC policy and can give one vector of per-leaf page slot counts
for every native batch. The vector length must match the completed
batch count. Leaf paths, partition validation and resource limits follow
the original Parquet writer.

## Guarantees and checks

`convert_readback` binds the original schema and batch frames through
exact EOS to the native file writer's construction and readback.
`Readback.file` exposes the same declarations and ordered batch
observations on the emitted bytes, with the exact group count and
original `GroupWire` for each group. `convert_terminal_wire` binds the
retained prefix and failure to the original stream cursor chain.
`round_trip` composes successful conversion with the existing native
Parquet-to-IPC route. It preserves positional declarations, logical
rows, explicit batch counts and exact EOS at both ends. Its premises
require both conversions to succeed under their respective budgets.

Pinned PyArrow supplies six genuine IPC streams. The three admitted
round trips read complete Lean Parquet files and Lean's returned
native IPC directly. Thrift and independent frame inspection check
the Parquet extents and levels and both streams' original batch
cursors. The fixtures include both signed widths' endpoints, distinct
null and empty nested values, unequal sibling cuts inside a List, the
authentic [3, 0, 2] batch sequence and a schema-only stream. Eight
labeled IPC edits and limit probes exercise sixteen typed refusals.
Late errors retain the original three-row batch and the authentic
empty batch even under exhausted writer limits and invalid cut
options. Valid nested LIST and positive-row width-zero IPC streams
reach the respective Parquet schema refusals.

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-from-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-from-ipc-oracle/check.py
```
