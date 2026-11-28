# Bounded predecessor functions in TLA+

Import [`DataElab.NamedFunctions.Thms`](../../Silmaril/Logic/Temporal/TLA/DataElab/NamedFunctions/Thms.lean).
A `Definition` supplies the value at zero and an ordered list of successor
bodies. Each body either returns the preceding value or replaces an existing
key of it with a supplied value. A list of length `n` declares exactly the
tagged integer interval `0 .. n`. The singleton interval admits the base case
alone. The step list contains tagged data and a choice of the two body forms.

## Reference rule

*Specifying Systems* introduces `f[x \in S] == e` in §5.5 and presents the
ordinary constructor and named form in §16.1.7. Section 6.3, equation (6.3),
defines the named form as `CHOOSE f : f = [x \in S |-> e]`. If the equation
has no witness, that choice can yield an unspecified value. Sections 16.1.5
and 17.4 give the same abbreviation inside LET, where the body of IN sees
the resulting definition in the enclosing context. Section 17.5.4 uses
the same equation for global and LOCAL module declarations.
[§5.5](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=72) ·
[§6.3](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=85) ·
[§§16.1.5, 16.1.7](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=317) ·
[§17.4](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=344) ·
[§17.5.4](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=348)

`Definition.FixedPoint` is the equation over tagged values with
`Graph.ofFn` as the anonymous constructor. In the positive case `i + 1`,
the predecessor `i` is in the interval and `Nat.lt_succ_self` proves the
strict decrease. Graph extensionality and induction on the index establish
existence and uniqueness on the exact domain. `Definition.choose_eq`
identifies the book's CHOOSE with that graph for any `ChoicePolicy` on the
tagged carrier. The unrestricted CHOOSE rule remains available at the
mathematical value layer for other predicates.
[Tagged graph laws](tla-functions.md)

## WriteThroughCache.vmem

The bridge captures the state values `wmem` and `memQ = Value.tuple entries`.
The following equations check the interpretation of the local function and
its use, including the order of the branches.

| Pinned expression | Checked equation |
| --- | --- |
| `0 .. Len(memQ)` | `vmem_rhs_domain` identifies the declared domain using the existing sequence and interval laws. |
| `IF i = 0 THEN wmem` | `vmem_rhs_zero` gives the result at zero for every candidate. |
| `memQ[i][2].op = "Rd"` and both uses of `f[i-1]` | `vmem_rhs_succ` uses one-based graph selection at key `j + 1`, component 2, and the string key `"op"`. Subtracting 1 on that positive integer gives exactly the recursive key `j`. |
| `[f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]` | The same equation uses the landed singleton EXCEPT law with the request's `"adr"` and `"val"` fields. |
| `IN f[Len(memQ)]` | `vmem_eq_choose_apply_len` selects the last key of the unique local graph. |

The branch equation holds for any candidate and every positive key of the
declared interval. It uses the fixed policy supplied for graph application
and update. For reference readings that rely on the queue schema, each
entry has its request at component 2 with an `op` field, and the write
branch selects `adr` and `val` from that request. The tagged operations
carry their existing unspecified outcomes on malformed operands. The contract is pointwise in the supplied state values.
[Book Figure 5.5b and §5.6](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=76) ·
[Pinned WriteThroughCache lines 54–61](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/CachingMemory/WriteThroughCache.tla#L54-L61)

## Source profile

`NamedFunctions.Source.checkSelected` takes a root registry entry and its
original operator unit index. It keeps the parsed root intact, resolves its
imports and the selected body, and checks the levels of the selected nullary
state operator. The function name is in scope in its recursive body and the
IN expression. The single index binder
is in scope in the function body. The declared domain uses the preceding
scope. The level checker infers the named value's level with self at constant
level, then checks the body again with self at the inferred level.
[Source checker](../../Silmaril/Logic/Temporal/TLA/DataElab/NamedFunctions/Source/Defs.lean)

Ordinary collection lowering supplies the bound, function body and IN
expression. The checker matches their expanded shape and verifies the exact
resolved identities of `..`, binary `-` and `Len`, the two state variables,
and all recursive and index witness uses. It admits the zero/read/write
shape in the table above, including renaming of the lexical binders. The
certificate ties the inspected syntax to the evaluator term. At every
positive integer key in the interval, `predecessor_key` proves that the
checked subtraction yields a smaller key still in the interval.
[Pinned Naturals](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Naturals.tla) · [Pinned Sequences](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Sequences.tla)

The collection evaluator runs the resulting anonymous function under CHOOSE
and applies the chosen graph in IN. With a tuple-valued source queue,
`CheckedVMem.eval_eq_choose_apply_len` identifies the predicate for every
candidate, and `CheckedVMem.eval_eq_vmem` applies the existing uniqueness
theorem. Both state inputs come from the source valuation at their resolved
IDs. The theorem allows an arbitrary target valuation. The depth bound
limits ordinary syntax expansion. The predecessor computation uses the
checked decreasing index.
[Source theorem API](../../Silmaril/Logic/Temporal/TLA/DataElab/NamedFunctions/Source/Thms.lean)

The WriteThroughCache gate first resolves unit 12 against all three intact
`EXTENDS` sources. It checks the `MemoryInterface` declaration origins and
the `Sequences` unit 0 `LOCAL INSTANCE Naturals` plan. That plan reuses the
original Naturals identities inside Sequences and keeps them local. The bound
and both recursive branches refer to the original Naturals `..` and binary
`-` declarations. Both calls to `Len` refer to its original Sequences
declaration.

The semantic pass supplies the existing interpreted signatures for Naturals
and Sequences, matched to the declarations by module identity, name, and
arity. It keeps the real `MemoryInterface` import. The upstream placeholder
definitions supply declaration evidence only. The certificate uses the original
`vmem` LET and the original `wmem` and `memQ` variable sites. The small
projection from #5394 also runs as a regression.
[Operator selection](tla-module-resolution.md#selecting-a-root-operator) ·
[Selection and origin checks](../../tests/semantics/tla-named-functions/WriteThroughCache.lean)

### Whole-module limits

| Original declaration or edge | Current limit |
| --- | --- |
| WriteThroughCache unit 2, `ASSUME (QLen \in Nat) /\ (QLen > 0)` | Full registry resolution rejects the assumption. Operator selection can pass it because the anonymous assumption introduces no names. |
| WriteThroughCache unit 3, `M == INSTANCE InternalMemory WITH mem <- wmem` | `InternalMemory` resolves independently and contains `THEOREM ISpec => []TypeInvariant`. The INSTANCE profile rejects a target with a theorem. A selection that uses `M!IInit` is also rejected because no instance members were admitted. |
| WriteThroughCache unit 19, `LM == INSTANCE Memory` | The intact `Memory` registry entry fails at unit 0, `Inner(mem, ctl, buf) == INSTANCE InternalMemory`, with the same theorem restriction. |

Both paths through `InternalMemory` also inherit the four-argument constants
`Send` and `Reply` from `MemoryInterface`. The first-order instance
substitution checker rejects operator-valued parameters, including implicit
ones. The later `Memory.Spec` also uses temporal existential quantification,
which the current INSTANCE syntax profiles do not admit. The selected
state certificate covers `vmem`. Primed or action-level uses, other recursive
bodies, top-level named functions, and refinement remain open.
[Instance contract](tla-module-instantiation.md) ·
[Pinned MemoryInterface](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/CachingMemory/MemoryInterface.tla) ·
[Pinned InternalMemory](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/CachingMemory/InternalMemory.tla) ·
[Pinned Memory](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/CachingMemory/Memory.tla)

## Checks

```sh
python3 -I tests/semantics/tla-named-functions/check.py
```

The gate verifies SHA-256 pins for all six source files at one upstream
revision. Controls cover skipped bodies, duplicate declarations, anonymous
INSTANCE scope, alpha-renaming, non-decreasing indices, wrong primitive
identities, and lexical scope. It audits the predecessor and CHOOSE theorems'
axiom closures. The value examples cover the empty queue, reads interleaved
with repeated writes, and a candidate with the wrong domain.
[Checked examples](../../Silmaril/Logic/Temporal/TLA/DataElab/NamedFunctions/Examples.lean) · [Pinned-source check](../../tests/semantics/tla-named-functions/check.py)
