module

public import Silmaril.Wasm.Component.IR.Defs

/-!
# Dead instance elimination: the transformation

On the flat IR, a core instance is *dead* when no later instance and no export
calls one of its functions. `removeNode l k` removes the `k`-th instance if it
is dead, renumbering the later references (`Impl.unshift`).
`deadInstances l` tries every instance, from the last to the first, so that a
chain of instances only used by dead instances disappears in one sweep.

In this model an instance does nothing until it is called (start functions
are not modelled), so removing a dead instance preserves the denotation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- The `Impl` does not call the functions `[e, e + w)`. -/
def Impl.avoids (e w : Nat) (im : Impl) : Bool :=
  match im.target with
  | .call r => !(decide (e ≤ r) && decide (r < e + w))
  | .const _ => true

/-- Renumber the references above `[e, e + w)` after removing these functions. -/
def Impl.unshift (e w : Nat) (im : Impl) : Impl :=
  match im.target with
  | .call r => if r < e then im else ⟨im.chain, .call (r - w)⟩
  | .const _ => im

/-- Remove the `k`-th instance if it is dead. -/
def removeNode (l : Linked M) (k : Nat) : Option (Linked M) :=
  match l.nodes[k]? with
  | none => none
  | some n =>
    let pre := l.nodes.take k
    let post := l.nodes.drop (k + 1)
    let e := linkedEnv l.imports.length pre
    let w := (CoreModule.exports n.1).length
    if post.all (fun n => n.2.all (Impl.avoids e w)) &&
        l.exports.all (fun x => x.impl.avoids e w) then
      some ⟨l.imports, pre ++ post.map (fun n => (n.1, n.2.map (Impl.unshift e w))),
        l.exports.map fun x => { x with impl := x.impl.unshift e w }⟩
    else none

/-- Remove dead instances, from the last to the first. -/
def deadInstances (l : Linked M) : Linked M :=
  (List.range l.nodes.length).reverse.foldl (fun l k => (removeNode l k).getD l) l

end Silmaril.Wasm.Component
