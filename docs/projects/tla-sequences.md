# TLA+ Sequences profile

The mathematical interpretation uses the graph convention in *Specifying
Systems* §18.1. A sequence is a function whose domain is exactly `1..n` for
some natural number `n`. `Graph.tuple_of_domain` proves that every such graph
has a tuple representation. `Value.tuple_injective` gives uniqueness.
`SetData.sequences S` is the union over natural lengths of the function
sets `[1..n -> S]`. Its membership laws give both that union equation and
the equivalent condition that every element of a tuple belongs to `S`.
The length zero graph is included even for an empty alphabet.
[Reference §18.1](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=357) ·
[Mathematical definitions](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Sequences/Defs.lean) ·
[Checked laws](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Sequences/Thms.lean)

| Operator | Admissible inputs and result |
| --- | --- |
| `Seq(S)` | A recognized tagged set. Returns the tagged set of all finite sequences over it. |
| `Len(s)` | A recognized sequence graph. Returns its natural length as a tagged integer. |
| `Append(s, e)` | A recognized sequence graph and any tagged element. Places the element at the new last position. |
| `Head(s)` | A recognized graph with key `1`. Uses the reference application `s[1]` and returns that value. |
| `Tail(s)` | A recognized nonempty sequence graph. Removes the first element and reindexes from `1`. |

For other operands the corresponding operation returns the fixed
`SequencePolicy` value for the operation and its original operands. This
includes `Head(<<>>)` and `Tail(<<>>)`. `Len`, `Append`, and `Tail` recognize
exactly the sequence domains above. The interpretation is mathematical and
noncomputable. [Tagged operator definitions](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Sequences/Defs.lean)

## Library identity and source check

The adapter uses separate revision-qualified identities for `Sequences` and
`Naturals` at TLA+ revision `bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`.
It gives the resolver signature-only modules, admits the five sequence
operators plus `Nat`, `<` and `\leq` from Naturals, and maps the resolved
declaration IDs to their tagged interpretations. Each expression argument
contributes to its result level, up to action level. The client supplies the
link from source import names to these identities. The fixture verifies the
standard files' exact hashes, parsed declarations and arities, and
Sequences' `LOCAL INSTANCE Naturals`, which introduces no exports. The
standard definitions supply reference equations for the interpretation.
[Pinned Sequences](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Sequences.tla) ·
[Pinned Naturals](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Naturals.tla) ·
[Adapter](../../Silmaril/Logic/Temporal/TLA/DataElab/Sequences/Defs.lean)

The gate parses the complete pinned BoundedQueue fixture. For resolution and
level checking it projects exactly two units, retaining their zero-based
positions and expression trees. Unit 2, the anonymous
`ASSUME Capacity \in Nat`, becomes an anonymous proof-free statement. Unit 9, the named theorem
`QueueSafety`, becomes an anonymous proof-free statement with the original
`Spec => []TypeOK` body. The projection checks the assumption shape and the
theorem name, expression form and presence of a proof. All constants,
variables and definitions keep their source units. The statement selector
reads the two projected expressions back from the checked registry.

Lean proves that the denoted source assumption holds exactly when Capacity
is a tagged natural. The model also interprets Messages as a tagged set,
which is the domain of the standard `Seq` equation. This interpretation
premise is separate from the source module's sole Capacity assumption. The result allows every fixed malformed-operand policy in this
profile over those rigid values and arbitrary behaviors of the tagged state
space.

The collection equations give the empty initial tuple, the member-and-length
invariant, and the guarded append and dequeue steps. The temporal lowering
yields `Init /\ [][Next]_q /\ WF_q(Dequeue)`. Lean checks both observations
against the resolved `q` coordinate and checks the theorem's implication and
always modality. Induction uses the source square action, so an idle step
needs equality of `q` alone. Weak fairness is interpreted as part of the
source specification and the invariant proof needs only the initial and
step conjuncts. Lean proves satisfaction of the denoted theorem under the
premises above. The source proof steps, including `PROOF OMITTED`, are
outside the check, as are queue liveness theorems. The sequence signature
admits `Head`, which the queue does not call. Concatenation, `SubSeq`,
`SelectSeq` and recursion remain outside the profile.
[BoundedQueue source](../../tests/semantics/tla-parser/BoundedQueue.tla) ·
[Lean fixture](../../tests/semantics/tla-sequence-source/BoundedQueue.lean) ·
[Temporal bridge](tla-data-temporal.md)

| Input | SHA-256 |
| --- | --- |
| BoundedQueue | `a92c8cfcb94e6a88b96d2d260def76c66bdffb45472c5df1a50c6223640ecccf` |
| Naturals | `73f2a68412039aa86f37ad08f0d0fef50fa8327d0ad8806f515548c75e9d9d84` |
| Sequences | `f613cffe14133769f0972b6f6e0139aaf0773004a51bac88ada382426e3eb7f4` |

```sh
python3 -I tests/semantics/tla-sequence-source/check.py
```

The gate builds with warnings as errors and audits the sequence and queue
theorems for dependencies on axioms beyond the three allowed by project policy.
It runs in `make check` with the library, sequence profile or DataElab
temporal targets.
[Gate](../../tests/semantics/tla-sequence-source/check.py) · [Axiom policy](../../policy.toml)
