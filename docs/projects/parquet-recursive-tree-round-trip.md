# Observational round trips for signed Tree Parquet and Arrow V5 IPC

The laws in `Parquet.RecursiveSchema.Tree.RoundTrip.Thms` apply when
both existing bridges succeed. They use the shared Arrow Events
projection and the existing strict IPC and native Tree readback
certificates.

## IPC to Parquet to IPC

`ipc_identity` recovers the original ordered recursive declaration and
the complete list of batch observations. Every observation carries its
explicit row count and belongs to the same batch position, including
zero-row batches. Both the original and returned streams have an exact
EOS at the end of their respective bytes.

`ipc_projected` recovers the declaration and batch observations of
`Arrow.RecursiveSchema.Stream.Events.projectTrace` applied to the
original strict IPC trace. The view addresses original top-level column
positions and can reorder, omit or repeat them. A width-zero view keeps
every original batch boundary and row count. The intermediate Parquet
read uses the native reader limits from the writer's readback
certificate. The original and returned IPC streams can use
independent IPC limits.

## Parquet to IPC to Parquet

`parquet_identity` uses the full positional view. It preserves the
recursive declaration and the number and order of original physical
groups. At each ordinal both checked native group reads have the same
explicit count, rows and ordered per-leaf repetition, definition and
signed word traces. The checked canonical LIST and Struct grammar
determines the physical leaf plan from the Arrow declaration. The
existing Tree projection gives the same signed traces under both
successful reads even when their schema depth limits differ.

This is a law for group and leaf observations. File bytes, page
boundaries, codecs and footer metadata can differ. Each native file
uses its own schema and row-group limits. The intermediate IPC
uses the same limits for the exporting and importing bridges.

The reverse writer's declaration and output limits still apply.
For example, an empty selection or a selection that repeats a field
can successfully export IPC and receive a typed native declaration
refusal on reimport. A supported schema-only carrier has zero groups
and a physical zero-row group retains its own ordinal.

## Verification

The composition oracle reuses the pinned PyArrow V5 mixed and
schema-only IPC streams and independently produced native samples
from the signed Tree scalar and Events oracles. The Parquet inputs
include genuine V2 and schema-only files plus the existing labeled
physical zero-row reframe. The oracle checks seven returned IPC
streams against Arrow Events, PyArrow and independent exact EOS
inspection. It checks native signed slot equality, returned Parquet
rows and original V1 page encodings for three native round trips.
It also verifies both reverse declaration refusals.

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-round-trip-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-round-trip-oracle/check.py
~~~
