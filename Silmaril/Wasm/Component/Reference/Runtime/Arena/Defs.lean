module

/-!
# Append-only arenas

The generic storage used by the component-model runtime store (`Runtime.CStore`)
for its runtime objects (instances, tasks, threads, subtasks, stream ends,
waitable sets, error contexts, ...). The Python reference
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
keeps these as heap objects referenced by Python identity; here an object is an index
into an `Arena`, wrapped in one of the id structures of `Runtime/Ids.lean`.

An arena is a plain list. It is append-only: `alloc` returns the current length
as the fresh index and nothing is ever removed, so an index once handed out
stays valid and is never reused (ids are unforgeable by construction; object
death is recorded in the object's own state, not by freeing its slot). `set`
and `modify` out of range are no-ops, like `List.set`/`List.modify`.

Not modelled: garbage collection or reuse of dead slots, and any bound on the
number of objects (the handle limit `Table.maxLength` concerns handle tables,
not arenas).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

universe u

/-- An append-only arena: object `i` is the `i`-th element. -/
abbrev Arena (α : Type u) := List α

namespace Arena

variable {α : Type u}

/-- The empty arena. -/
def empty : Arena α := []

/-- Append `x`, returning the new arena and the index of `x` (the old length). -/
def alloc (a : Arena α) (x : α) : Arena α × Nat := (a ++ [x], a.length)

/-- The object at index `i`, if allocated. -/
def get? (a : Arena α) (i : Nat) : Option α := (a : List α)[i]?

/-- Replace the object at index `i` (no-op when `i` is not allocated). -/
def set (a : Arena α) (i : Nat) (x : α) : Arena α := List.set a i x

/-- Update the object at index `i` (no-op when `i` is not allocated). -/
def modify (a : Arena α) (i : Nat) (f : α → α) : Arena α := List.modify a i f

theorem get?_eq_getElem? (a : Arena α) (i : Nat) : a.get? i = (a : List α)[i]? :=
  rfl

@[simp] theorem length_alloc (a : Arena α) (x : α) :
    List.length (a.alloc x).1 = a.length + 1 := by
  simp [alloc]

@[simp] theorem alloc_snd (a : Arena α) (x : α) : (a.alloc x).2 = a.length := rfl

@[simp] theorem get?_alloc_self (a : Arena α) (x : α) :
    (a.alloc x).1.get? (a.alloc x).2 = some x := by
  simp [alloc, get?_eq_getElem?]

@[simp] theorem length_set (a : Arena α) (i : Nat) (x : α) :
    List.length (a.set i x) = a.length := List.length_set ..

@[simp] theorem length_modify (a : Arena α) (i : Nat) (f : α → α) :
    List.length (a.modify i f) = a.length := List.length_modify ..

end Arena

end Silmaril.Wasm.Component.Runtime

namespace Silmaril.Wasm.Component.Runtime

universe u

namespace Arena

variable {α : Type u}

theorem get?_modify_self (a : Arena α) (i : Nat) (f : α → α) :
    (a.modify i f).get? i = (a.get? i).map f := by
  simp [modify, get?_eq_getElem?]

theorem get?_modify_ne (a : Arena α) {i j : Nat} (f : α → α) (h : i ≠ j) :
    (a.modify i f).get? j = a.get? j := by
  simp [modify, get?_eq_getElem?, h]

end Arena

end Silmaril.Wasm.Component.Runtime
