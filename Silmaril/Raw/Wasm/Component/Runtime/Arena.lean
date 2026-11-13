module

public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Defs

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

namespace Arena

variable {α : Type u}

theorem get?_alloc_lt (a : Arena α) (x : α) {i : Nat} (h : i < a.length) :
    (a.alloc x).1.get? i = a.get? i := by
  simp [alloc, get?_eq_getElem?, List.getElem?_append_left h]

/-- Indices at or beyond the length are unallocated; in particular the index the
next `alloc` returns is fresh. -/
theorem get?_of_le (a : Arena α) {i : Nat} (h : a.length ≤ i) : a.get? i = none := by
  simp [get?_eq_getElem?, h]

theorem alloc_fresh (a : Arena α) : a.get? a.length = none := a.get?_of_le (Nat.le_refl _)

theorem get?_set_self (a : Arena α) {i : Nat} (x : α) (h : i < a.length) :
    (a.set i x).get? i = some x := by
  simp [set, get?_eq_getElem?, h]

theorem get?_set_ne (a : Arena α) {i j : Nat} (x : α) (h : i ≠ j) :
    (a.set i x).get? j = a.get? j := by
  simp [set, get?_eq_getElem?, h]

example : Arena.alloc (Arena.alloc ([] : Arena Nat) 7).1 9 = ([7, 9], 1) := by decide +kernel
example : Arena.modify ([7, 9] : Arena Nat) 1 (· + 1) = [7, 10] := by decide +kernel
example : Arena.get? ([7, 9] : Arena Nat) 2 = none := by decide +kernel

end Arena

end Silmaril.Wasm.Component.Runtime
