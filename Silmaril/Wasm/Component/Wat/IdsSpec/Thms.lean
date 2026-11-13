module

public import Silmaril.Wasm.Component.Wat.IdsSpec.Defs
public import Silmaril.Proofs.Wasm.Component.Wat.IdsSpec

/-!
# Component WAT identifiers: `resolve` assigns the right indices

Proofs in `Silmaril.Proofs.Wasm.Component.Wat.IdsSpec`:

* `count_addAll`: after the allocations `L`, a scope counts `countIn L sp` more items
  of space `sp`;
* `lookup_addAll_iff`, `lookup_fresh_iff`: in a scope that starts without names, `x`
  names index `i` of `sp` after `L` exactly when `NamesIdx L sp x i`: the last binder
  `(sp, x)` of `L` has `i` allocations of `sp` before it;
* `rItemsAt_list`, `rItemsAt_scope`: `rItemsAt` resolves item `k` of a scope (a list
  `(xs)`) with `rItem` in the scope of the allocations of items `0 … k-1`
  (`allocsOf`), and its result is element `k` of the output;
* `rAtom_scope_iff`: hence an identifier `$x` read in space `sp` in item `k` of a
  component or type scope resolves to the numeral `i` exactly when
  `NamesIdx (allocsOf ty (items.take k)) sp x i`.

What each item allocates (`itemAllocs`, through `defOf` and `startValues`) and which
space a reference is read in (`rRefs`, `ctxSpace`) follow `Explainer.md` as
documented in `Silmaril.Wasm.Component.Wat.Ids.Defs`; that correspondence is a
transcription, checked by the tests in `tests/wat/Ids.lean`, not a theorem.
Duplicate binders are not rejected (the last one wins).
-/
