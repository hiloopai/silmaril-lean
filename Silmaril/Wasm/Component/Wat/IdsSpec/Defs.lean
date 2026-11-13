module

public import Silmaril.Wasm.Component.Wat.Ids.Defs

/-!
# Component WAT identifiers: the index specification

`Silmaril.Wasm.Component.Wat.resolve` keeps one `Scope` per enclosing component or type
and adds the items of a scope to it one after the other. This module states, as
data, what each item allocates and which index a name then denotes:

* `itemAllocs inType it`: the allocations of one item, in order: the item's space and
  binder (`defOf`), then one value per `start` result;
* `allocsOf inType items`: the allocations of a list of items;
* `NamesIdx L sp x i`: after the allocations `L`, the identifier `x` names index `i`
  of space `sp`: `L` contains a binder `(sp, x)` with no later binder `(sp, x)` (the
  last binder wins: WAT forbids duplicates, `resolve` does not check them), and `i`
  allocations of space `sp` precede it.

The theorems (`Silmaril.Wasm.Component.Wat.IdsSpec.Thms`) say that the scope in which
`resolve` reads item `k` of a scope is the scope of the allocations of items `0 … k-1`,
and that in it an identifier is looked up exactly as `NamesIdx` says.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

/-- What one allocation adds to a scope. -/
abbrev Alloc := Space × Option String

/-- The allocations of one item: its space and binder, then one value per `start`
result. -/
def itemAllocs (inType : Bool) : Sexp → List Alloc
  | .list xs =>
    ((defOf inType xs).1.map fun sp => (sp, (defOf inType xs).2.2)).toList ++
      List.replicate (startValues xs) (.value, none)
  | _ => []

/-- The allocations of a list of items. -/
def allocsOf (inType : Bool) (items : List Sexp) : List Alloc := items.flatMap (itemAllocs inType)

/-- A scope after the allocations `L`. -/
def Scope.addAll (s : Scope) (L : List Alloc) : Scope := L.foldl (fun s e => s.add e.1 e.2) s

/-- The number of allocations of space `sp` in `L`. -/
def countIn (L : List Alloc) (sp : Space) : Nat := (L.filter fun e => e.1 = sp).length

/-- After the allocations `L`, identifier `x` names index `i` of space `sp`. -/
def NamesIdx (L : List Alloc) (sp : Space) (x : String) (i : Nat) : Prop :=
  ∃ L1 L2, L = L1 ++ (sp, some x) :: L2 ∧ i = countIn L1 sp ∧ (sp, some x) ∉ L2

end Silmaril.Wasm.Component.Wat
