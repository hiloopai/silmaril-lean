# Pinned ACP_SB state and transition denotations

The fixture proves exact graph-schema equations for `Init` and `TypeInv`
from intact ACP_SB. Under the explicit model premise
`participants.asSet = some P`, the initial-state denotation implies the
type invariant at the same state, and every `progN` step from a state
satisfying `TypeInv` takes it to a state satisfying `TypeInv`. The proofs
allow any tagged set `P`, including the empty set and infinite sets. Other
rigid values may coincide, and flexible valuations and fixed adapter
policies are arbitrary.

## Source and selection

The source is the upstream ACP_SB example at TLA+ revision
`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`, under
`tlatools/org.lamport.tlatools/test-model/examples/acp/ACP_SB.tla`.
Its SHA-256 is
`a62fedef4725c150efd03f5a864bb607f2f3960686b518792144e1d781c6de89`.
[Pinned source](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/acp/ACP_SB.tla)

The native parser reads the hash-verified file. `Resolution.Instances.check`
resolves and level-checks the complete module and retains all 40 source
units. `Collections.lowerState` selects the original nullary state
definitions by their IDs at units 7 (`Init`) and 4 (`TypeInv`), counting
from zero. `Collections.lowerAction` selects `progN` at unit 24 from the
same registry. All three selections use empty external signatures. The
expanded terms are quoted as Lean data and their well-formedness proofs
are checked by the kernel.
[Resolution](tla-acp-sb-resolution.md) · [Collection lowering](tla-data-elab.md#state-level-collection-expressions)

## Exact graph schemas

Under the set-shape premise, each state predicate holds precisely when
the two flexible values have the following shapes.

- `participant` is a graph with domain exactly `P`. Each output is a record
  with the five keys `vote`, `alive`, `decision`, `faulty` and `voteSent`.
  The field bounds are the ones in the selected source definition.
- `coordinator` is a record with the six keys `request`, `vote`, `broadcast`,
  `decision`, `alive` and `faulty`. The first three fields are graphs whose
  domains are exactly `P`. Their ranges and the remaining three field
  bounds come from the selected definition.

The Lean equations state exact record domains and per-field lookup membership,
using the [tagged record-set laws](tla-record-sets.md) and [function-set
laws](tla-functions.md). The proof of `Init → TypeInv` reuses the same
participant graph and coordinator record. It preserves their domains and
widens each field range. The two coordinator schemas list their fields in
different orders and have the same exact key set.

DataBridge supplies rigid and flexible lookups by declaration identity and
lifts the selected predicates to General TLA state formulas. The equations
and implication hold at any instant of an arbitrary behavior with one rigid
valuation. The checked implication is a state obligation.
[DataBridge](tla-data-bridge.md)

## The eleven transition actions

The source uses `progN` as the action subscripted by the state tuple in
`Spec`. The gate follows its resolved disjunctions and the two existential
binders over `participants`. It checks the leaf declaration identities
and the references that pass each bound participant to the action bodies.

| Source path | Leaf actions |
| --- | --- |
| `parProgN`, under `\E i \in participants` | `parDie(i)` (18) |
| `parProgN → parProg(i)`, under the same binder | `sendVote(i)` (14), `abortOnVote(i)` (15), `abortOnTimeoutRequest(i)` (16), `decide(i)` (17) |
| `coordProgN` | `coordDie` (13) |
| `coordProgN → coordProgB` | `makeDecision` (11), with two guarded writes |
| `coordProgN → coordProgB → coordProgA(i)`, under `\E i \in participants` | `request(i)` (8), `getVote(i)` (9), `detectFault(i)` (10), `coordBroadcast(i)` (12) |

`progN_holds_iff` checks the denoted relation against these cases under
the current-state graph schemas. The checked equation includes the guards,
including the universal request and voting tests and the existential
no-vote test, and both endpoint equations in each branch. Primes read the
target valuation. The unprimed guards and update operands read the current
valuation. The collection lowerer evaluates `UNCHANGED e` as equality
between the primed and current values of `e`, including the singleton
tuple observations in these actions.

Nested `EXCEPT` evaluates each lexical `@` at its old leaf. The exact
equation retains the ordered writes to `alive` and `faulty` in the death
actions. The preservation proof uses graph update laws to retain exact
domains and all sibling values. It checks the bound of each replacement.
In particular, `getVote` uses the participant's typed vote, and
`coordBroadcast` and `decide` use their inequality guards to exclude
`undecided` and `notsent`, respectively. [Graph updates](tla-functions.md) · [EXCEPT semantics](tla-except.md)

`progN_preserves_typeInv` applies the checked step equation at adjacent
instants of an arbitrary behavior. This gate covers every disjunct of
the raw action. Temporal selection of ACP_SB's `Spec`, including its
always-square action and the `fairness` clause's participant-indexed
`WF`, is outside the gate. Source correctness statements and proofs
remain outside its scope. [Temporal lowering](tla-data-temporal.md)

## Reproduce

```sh
make tla-acp-source-check
```

The driver reuses the native parser fixture pin and temporary download
verification. It builds the fixture's dependencies with warnings as
errors and runs the Lean checks. The gate rejects any theorem axiom outside
`propext`, `Classical.choice` and `Quot.sound`. `make check` runs it for
library builds and scoped TLA builds.
[Driver](../../tests/semantics/tla-acp-source-acceptance/check.py) · [Lean fixture](../../tests/semantics/tla-acp-source-acceptance/ACP_SB.lean)
