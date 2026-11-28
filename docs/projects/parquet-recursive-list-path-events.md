# Arrow Events for the native signed LIST path

`ListPath.Reader.Events.read` opens the original Parquet declaration
and exposes it once as a positional Arrow signature. Each complete
original row group yields one Arrow batch in footer order. An explicit
empty group yields a zero-row batch. A schema-only file emits the
declaration and EOS. For a populated source, EOS follows only after
all original groups succeed.
[Native V1 reader](parquet-recursive-list-path-v1.md)

The reusable `Parquet.Reader.Recursive.Groups` adapter supplies the
shared typed Parquet reader with one checked recursive Arrow batch
per group. Its prefix law identifies the original read behind every
batch and the group and cause responsible for a read failure. ListPath
attaches the native group wire witness to every emitted batch.
A group failure retains the original error, address and any page
coordinates. The trace keeps all complete earlier groups and emits
no part of the failing group. An open failure precedes schema emission.

## Projection and reframing

`readProjected` selects the full original field or the empty schema.
Both selections validate the original bytes through the same group
reader. Empty projection retains each explicit row count, the complete
prefix and the original termination. Successful native reads with the
same declaration and ordered group observations yield equal direct
event streams and agree under the shared observation semantics for
both projections. This applies to the legal V1 reframes checked by
the native reader's trace law.
[Recursive Arrow Events](arrow-recursive-events.md)

The source profile is the unindexed UNCOMPRESSED PLAIN V1 LIST-path
reader. Projection operates on whole top-level fields. Indexed,
pageless, compressed and dictionary chunks remain outside this profile.

## Verification

The pinned oracle checks nine sources and 47 original pages. Genuine
PyArrow files cover both signed widths, depths three, four, six and
sixteen, nested nulls and empties, schema-only EOS and an absent page
CRC. A labeled file contains a physical empty group between two
populated groups. The existing labeled V1 reframe starts pages at
repetitions one, two and three and agrees with its original Events
under both projections.

Labeled later-page word and CRC failures preserve the first complete
group and the original group, column, page, byte and cursor coordinates
under both projections. An empty carrier exercises the typed open
failure.
[Producer and fixture pins](../../scripts/parquet-recursive-list-path-events-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-events-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-events-oracle/check.py
~~~
