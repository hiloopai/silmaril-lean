# Fixed-sort Peggy signatures

[`Dialect.Defs`](../../Silmaril/SSA/Peggy/Dialect/Defs.lean) defines
`Silmaril.SSA.Peggy.Dialect.FixedSortSignature Data`. An object supplies an
instruction alphabet indexed by ordered operand sorts and one result sort.
A morphism `f : S ⟶ T` maps each opcode forward in its own profile. Maps can
identify opcodes. Identity is pointwise identity, and `f ≫ g` applies `f`
first. Use `FixedSortSignature.ofOpcodeMap` to bundle a PEG instruction map
and `FixedSortSignature.opcodeMap` to use an arrow with `PEG.Graph.mapOps`.

A sentence `Equation S` compares two typed, open, structurally admitted PEGs
with common parameter and result lists and a common loop forest. The two sides
have independent vertex tables and root references. Each `OpenGraph` carries
`PEG.Graph.WellFormed` and an equality between its graph's parent table and the
specified forest. `Equation.map` relabels both sides at the shared boundary
and loop frame. The graph-level operation reuses the core's relabelling
and admission theorem.

[`Dialect.Thms`](../../Silmaril/SSA/Peggy/Dialect/Thms.lean) proves identity
and composition on equations and packages them in `sentenceFunctor`.
`Equation`, `Equation.map`, `Equation.map_id` and `Equation.map_comp` have the
shapes of `Sen`, `map`, `map_id` and `map_comp` in `Silmaril.Inst.Plain`,
respectively. A future discrete-model instance supplies the concrete `Mod`,
contravariant `reduct` and its laws, and `Sat` with `sat_map`. The latter must
relate satisfaction of the relabelled equation in a target model to
satisfaction of the source equation in its reduct. The guarded PEG evaluator
and its transport theorem supply the semantic step.
[Institution builders](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean)

## Extending to maps of sorts

The fixed-sort category covers opcode inclusions, renamings and identifications
where both dialects already agree on the sorts. It makes relabelling preserve
all dependent graph indices by construction and gives the upcoming reduct a
common type for each parameter environment and observation.

A variable-sort category would add a data-sort function `s : Data → Data'`.
Extend it to `PEG.Ty` by fixing `.bool` and `.count` and sending `.data d` to
`.data (s d)`. The opcode map then lands at the pointwise image of its ordered
operand list and at the image of its result sort. At the graph boundary, a
generalization of `OpenGraph.map` would transport parameter ports, vertex sort
declarations, operand and root tuples, and references along this function
while retaining vertex and loop identifiers. It would need edge-role and
admission invariance, plus identity and composition laws for those transports,
including when the sort map identifies two data sorts. The existing category
should embed as the arrows over the identity sort map. A corresponding model
reduct would pull back the target carriers along the sort map, with evaluation
transport at the resulting parameter and result types. Typed program
substitution needs a separate translation and semantics.

## Check the dialect

```sh
lake build --wfail +Silmaril.SSA.Peggy.Dialect.Thms PeggyDialectTests PEGCoreTests
lake env leanchecker Silmaril.SSA.Peggy.Dialect.Thms
```

The dialect fixture compares two open recurrences with theta feedback. It
identifies two distinct unary opcodes, renames their image in a third dialect,
and checks functoriality, admission, the loop frame and repeated roots.
[Lean fixture](../../tests/ssa/PeggyDialect.lean)
