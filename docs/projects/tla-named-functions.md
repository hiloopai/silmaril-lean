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

The bridge starts at interpreted state values and uses a direct translation
of this one LET expression. The pinned module parses, while the existing
resolver reports `.unsupported .functionDefinition` when it reaches a
named-function declaration. Source lowering would also need a resolved
primitive contract for binary `-` from `Naturals`. The bridge uses
integer subtraction only at positive interval keys. Whole-module resolution,
arbitrary named-function bodies and INSTANCE replay of this form are outside
the fragment.
[Resolver scope](tla-module-resolution.md#boundaries-and-checks) ·
[Pinned Naturals](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Naturals.tla)

## Checks

```sh
python3 -I tests/semantics/tla-named-functions/check.py
```

The check builds the Lean examples with `--wfail`, verifies the upstream
module SHA-256
`d63221a21377ee59c707dcf1ec05dd73be7616674343052a2b0d794b0c0526a2`,
and compares the parsed `vmem` body against the full LET expression used
to derive the bridge. The examples cover the empty queue, reads interleaved
with repeated writes, and rejection of a candidate with the wrong domain.
[Checked examples](../../Silmaril/Logic/Temporal/TLA/DataElab/NamedFunctions/Examples.lean) ·
[Pinned-source check](../../tests/semantics/tla-named-functions/WriteThroughCache.lean)
