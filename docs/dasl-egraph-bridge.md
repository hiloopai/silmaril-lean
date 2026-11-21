# Checked DASL e-graph tables

`Silmaril.Formats.Dasl.EGraph.Thms` interprets a checked `classId` table as
an e-graph partition. It does not interpret the parent profile. There must
be exactly one row per ordered DAG witness: row `i` names term `i`, and
its `e[i]` is that term's class label. Each row must satisfy a caller-supplied
decidable name-to-term relation; names need not be unique. The DAG, naming
relation, seed assertions and merge log are separate inputs to this check.

Shape and naming checks do not justify class equality. `certify?` starts
with singleton classes and checks each proposal in the supplied finite log
using the e-graph's one-step checker. A proposal can reference only the
preceding snapshot. The table must induce exactly the replayed equivalence,
irrespective of class numbering or unused labels. Acceptance proves soundness
for the guarded term PER, including the raw-ID interpretation, where invalid
IDs are outside the support.

`certified_reencode` transports accepted rows between recoverable codecs,
including raw rows, parallel columns and independently paged columns. It
preserves the certificate result and hence its interpreted PER and witnessed
names, not the DASL tree, serialized bytes or content hash.

Replay consumes the supplied list; it neither searches for missing merges
nor proves saturation, seed coverage or general completeness. This bridge
uses the existing `Partition` and exact merge contract; it supplies no
union-find implementation or serialized proof-log format.

Run `make check CHECK_TARGETS='+Silmaril.Formats.Dasl.EGraph.Thms'`. The fixture
has a countermodel for a structurally valid unproved collapse, then checks a
seed followed by a rebuild collision in flat and paged row and column layouts.
