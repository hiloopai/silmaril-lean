# Infer parent/child PEG boundaries from the original graph

`Schedule.Automatic.Regions.discover` infers typed cuts, exports, and
stage order from the original PEG and its designated roots. It takes
the opcode roles, an original demand rank, and the schedule search
budget. It reuses checked cut synthesis and the existing unit-counter
and parent/child leaf recognizers. This is a bounded placement step
toward [§7.2–7.5](https://arxiv.org/pdf/1012.1802v3#page=41).
[Graph-only entry](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Regions/Defs.lean)

## Region boundaries

The existing dependency ordering works on groups rooted at parentless
keys. Each labelled child is assigned to its labelled parent before
computing row ownership and interstage prerequisites. Each group can
contain a single child. Dependencies from child initializers to the
current outer tuple, and from child evals to the outer feedback, stay
in that group. The inference walks the complete ordered operand
closure, including feedback. Its backward pass propagates required
rows between groups and forwards them in row order. The final
projection selects the original roots in order, including repetitions.

A nested stage exports one distinct reference, an eval of its
parentless key. The root's closure at the proposed input cuts must
reach the child. Cut synthesis then retains all rows labelled by both
keys, including unread child evals needed for the checked child exit
bundle. Local rows and keys are remapped with the actual typed
operands and parent links.

The export test walks toward the first pass or eval and checks those
rows as well. A live θ, child pass, or child eval is tied to an active
frame and fails this test. Thus a later sibling may use the completed
outer eval while an exposed child eval is rejected. The leaf checker
validates the remaining intra-region wiring, including the old outer
store used by child initialization. Child resets and simultaneous commit retain
the semantics of the existing certificate.

The parentless entry from #4910 keeps its parentless restriction.
The new path is a heuristic for the existing checked leaf shapes.
Each nested stage's singleton exit bundle limits which values can
be forwarded across it. The order-search budget counts stage
attempts. Dependency inference and leaf checks have separate costs.
[Cut synthesis](peggy-sequential-cut-leaves.md)

## Finite-return agreement

A successful discovery carries the existing `Schedule.check` equation
on the original graph. With the declared Boolean negation law and,
for counted leaves, the zero and unit-tick laws,
`Found.observations_of_exec` proves that successful emitted SIMPLE
execution yields the original ordered Figure 11 outputs and first
exits. With the respective slice-definedness hypotheses,
`Found.exec_iff_observations` constructs a successful run from those
observations. A nested stage requires a defined child first exit at
each continuing outer activation. Defined primitive slices and finite
child exits are separate premises. The theorem concerns finite
successful returns.
[Checker equation](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Regions/Thms.lean) ·
[Finite-return theorems](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Thms.lean)

The anchor-free fixture runs the parent/child loop with child lengths
two and one and returns `[4]`. It repeats that check with both row and
loop IDs permuted. A stale child initializer fails the leaf checker.
In the mixed fixture, the completed parent result sets a later
unit-counter sibling's trip count, and the schedule returns
`[5, 4, 5]`. Replacing that dependency with a child eval yields an
explicit frame-local rejection on a graph that still passes its rank
check.
[Regressions](../../tests/ssa/PEGCanonicalWhile.lean)
