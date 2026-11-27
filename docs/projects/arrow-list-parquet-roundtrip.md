# Native Arrow LIST to Parquet and back

`Parquet.ListFile.Writer.FromIpc.convert` accepts the checked native Arrow V5
stream profile with one nullable `List<Int32>` field and a nullable signed
child. It passes the outer and child names from the stream to the canonical
Parquet LIST writer. A complete stream with a child name other than
`element` returns `.childName` with the original name. The writer emits one
uncompressed, CRC-free PLAIN Data Page V1 per input batch. A schema-only
stream produces zero row groups. An explicit empty batch produces one
zero-row group with a framed zero-slot page and two zero-length level
sections.
[Canonical Parquet writer](parquet-list-writer.md) · [Wire pins](arrow-parquet-coverage.md)

The converter finishes decoding the source, including exact EOS, before
checking the child name or running the writer. Any source error returns
`.source cause` with the original coordinates and error. The writer's typed
limits and refusals are then exposed as `.writer cause`. A failure returns
no Parquet bytes, even when earlier source batches were valid. Both format
profiles and limits come from their existing entry points.

`convert_source_error` and `convert_child_name` specify error precedence.
`convert_readback` witnesses the original IPC schema and batch framing
through EOS, the exact written layout, and successful native Parquet readback
in footer order. The native readback carries the original names and the
per-group wire witness at each input batch ordinal.
[Public API and proofs](../../Silmaril/Formats/Parquet/ListFile/Writer/FromIpc/Thms.lean)

`roundTrip` composes successful forward conversion with
`Parquet.ListFile.Multi.ToIpc.convert` using the same Parquet readback limits.
The returned IPC stream, read under its own supplied limits, has the same
field descriptor and ordered batch rows, including null lists, empty lists,
null children, signed values and empty batches. This equality concerns the
Arrow observation. The emitted stream has its own buffer coordinates and
contains only children of present lists. In the mixed fixture the first batch
has five physical children in the source, including a value hidden under a
null list, and four physical children after the round trip.
[Parquet to native IPC](parquet-list-to-ipc.md)

## Independent reproduction

PyArrow 26.0.1 produces the native IPC inputs and reads both the Lean-written
Parquet and the returned IPC. Apache Thrift 0.25.0 checks the footer schema
and physical path, the ordered frame extents, the two run sections and the
signed word suffixes. The comparator checks exact V5 IPC message boundaries
and EOS in both directions. It regenerates the pinned schema-only, empty
batch and noncanonical-child inputs byte for byte. The mixed fixture
includes both signed INT32 endpoints. A late truncated batch is rejected
with its original index even when the source also has an unsupported child
name or would exceed a sink limit.
[Pinned dependencies](parquet-column-index.md#pinned-independent-fixture) · [Byte hashes and observations](../../scripts/arrow-list-parquet-roundtrip/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Examples
python3 scripts/arrow-list-parquet-roundtrip/Oracle.py "$replay" |
  diff -u scripts/arrow-list-parquet-roundtrip/observations.txt -
```
