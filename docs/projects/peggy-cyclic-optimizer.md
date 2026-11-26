# Cyclic PEG self-feedback elimination

[`Optimizer.Cyclic.optimize`](../../Silmaril/SSA/Peggy/Optimizer/Cyclic/Defs.lean)
accepts a typed, nonempty PEG table with one loop. It searches for a θ whose
feedback operand is its own address and whose initializer is a distinct
zero-input node. At iteration zero θ reads the initializer. At each successor
iteration θ reads its own previous value. A parameter or nullary primitive
has no index-dependent operands, so its stream is invariant in the loop.
The invariant holds for partial nullary primitives even when they return
bottom. The implementation uses the guarded Figure 11 invariance and
self-feedback theorems for this rule.

## Admission and certificate

1. The source may contain parameters, primitive applications, φ and θ. The
   sole loop must have no parent. Admission estimates a nonfeedback phase
   with one synchronous update per row and checks all nonfeedback edges
   for descent. It independently checks native demands against the
   lexicographic rank of the loop counter and the phase. These checks
   establish the paper's structural `WellFormed` guard and well-founded
   demand. The profile excludes pass and eval.
2. The search visits each numbered row at most once. The matched row
   supplies one guarded equation to the [finite saturation kernel](peggy-saturation.md),
   starting from singleton classes. Literal self feedback discharges the
   class guard in the initial partition. The initializer test supplies the
   semantic invariance premise. `Match.rule_holds` and `Match.classes_valid`
   justify the merge for every interpretation and input.
3. Extraction deletes the matched row, compacts the addresses, and redirects
   its uses and output occurrences to the initializer. All other rows keep
   their original typed labels. The target goes through the same structural
   and demand checks on its own table. Extraction builds each selection
   witness from the retained source row and its redirected arguments. The
   [selection kernel](peggy-epeg.md) checks the classes of corresponding
   operands and ordered roots, then derives the target's Figure 11 equations.

[`Result.sound`](../../Silmaril/SSA/Peggy/Optimizer/Cyclic/Thms.lean)
equates the ordered tuples of partial Figure 11 results at every index,
under the same primitive interpretation and ordered input tuple. Repeated
roots and bottom are preserved. Primitive applications retain their strict
semantics, and φ retains its demand for only the selected arm.

## Scope and regression

The optimizer returns the first candidate that passes all checks. Every
success reduces stored row count by one, counting shared rows once. The pass
does not repeat the search on the target, remove unrelated dead rows, or
compare global costs. Matching is limited to literal self feedback with a
leaf initializer, and saturation has one ground obligation with one merge
of fuel. Nested loops, arbitrary invariant expressions, class-based matching,
node-generating saturation, and reversion to an imperative language remain
outside this pass.

The [regression](../../tests/ssa/PeggyEgg.lean) compacts seven rows to six,
redirecting shared uses and two ordered root occurrences while retaining a
live θ/successor counting cycle. A partial primitive initializer also
passes, and its self-feedback stream is proved bottom at iteration one.
An admitted near miss uses the live counter as initializer. The matcher
rejects it, and at iteration one its self-feedback row still denotes zero
while the initializer denotes one.

```sh
lake build --wfail +Silmaril.SSA.Peggy.Optimizer.Cyclic.Thms PEGCoreTests PEGRulesTests PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.Optimizer.Cyclic.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
