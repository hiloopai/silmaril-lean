module

public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Objects
public import Silmaril.Raw.Wasm.Component.Runtime.Arena

/-!
# The component store `CStore`

`Runtime.CStore E` is all component-level runtime state as plain data: the shared core-engine
store (whose host code is `CanonHost E`), one append-only `Arena` per REF runtime object kind
(instances, resource types, function values, tasks, threads, subtasks, resource handles,
stream/future ends, waitable sets, error contexts, callers), and the REF `Store` fields
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`, `Store`, L508-515,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>):
`waiting` (REF `store.waiting`, in append order), `nesting_depth` and `lockdown`. The
component store lives OUTSIDE the core store (issue #477). Continuations of blocked threads are
NOT part of it (they live in the machine).

Arena access is uniform: an `ArenaField E Id α` names one arena of the store together with its
id type, and `ArenaField.alloc`/`get?`/`set`/`modify` act on the store through it. The
lemmas (`get?_alloc`, `get?_alloc_self`, `length_alloc`, `get?_set`, `get?_set_self`,
`get?_set_ne`, `get?_modify`, ...) are proved once, generically, from the `Runtime.Arena`
lemmas, and hold for each of the eleven instances `ArenaField.insts`, ..., `ArenaField.callers`.
Accesses to different arenas commute definitionally (each `put` is a structure update of one
field), so cross-arena frame facts are `rfl`/`simp` on the concrete instances.

Not modelled here: readiness evaluation, candidate selection, store operations of the
REF (`invoke`, `tick`, `lift`, `lower`; `Embedding.lean`) and invariants.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

namespace CStore

variable {E : CoreEngine}

end CStore

namespace ArenaField

variable {E : CoreEngine} {Id α : Type} (F : ArenaField E Id α)

theorem get?_alloc_ne (s : CStore E) (x : α) {i : Id} (h : i ≠ (F.alloc s x).2) :
    F.get? (F.alloc s x).1 i = F.get? s i := by
  have hne : F.idx i ≠ F.size s := fun h' => h (F.idx_injective (by simp [h']))
  simp only [get?_alloc, hne, ite_false]

/-- The id the next `alloc` returns is unallocated. -/
theorem get?_fresh (s : CStore E) : F.get? s (F.mkId (F.size s)) = none := by
  simp [get?, size, Arena.get?_of_le]

section DecEq

variable [DecidableEq Id]

theorem get?_set_self (s : CStore E) (i : Id) (x : α) (h : (F.get? s i).isSome) :
    F.get? (F.set s i x) i = some x := by
  simp only [get?_set, ite_true]
  cases hx : F.get? s i <;> simp_all

theorem get?_set_ne (s : CStore E) {i j : Id} (x : α) (h : i ≠ j) :
    F.get? (F.set s i x) j = F.get? s j := by
  simp only [get?_set, h, ite_false]

end DecEq

/-! ### The eleven arenas of `CStore` -/

end ArenaField

namespace CStore

variable {E : CoreEngine}

/-! ### Tests -/

example : (ArenaField.tasks.alloc (empty : CStore E)
    { ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }).2 = ⟨0⟩ := rfl

example (x y : Thread) :
    let s₁ := (ArenaField.threads.alloc (empty : CStore E) x).1
    let r := ArenaField.threads.alloc s₁ y
    r.2 = ⟨1⟩ ∧ r.1.thread? ⟨0⟩ = some x ∧ r.1.thread? ⟨1⟩ = some y ∧
      r.1.thread? ⟨2⟩ = none ∧ r.1.tasks = [] := ⟨rfl, rfl, rfl, rfl, rfl⟩

example (x : WaitableSet) :
    let s := (ArenaField.wsets.alloc (empty : CStore E) x).1
    (ArenaField.wsets.modify s ⟨0⟩ fun w => { w with numWaiting := w.numWaiting + 1 }).wset?
      ⟨0⟩ = some { x with numWaiting := x.numWaiting + 1 } := rfl

/-- Allocating in one arena leaves the other arenas and the `Store` fields unchanged. -/
theorem threads_alloc_frame (s : CStore E) (x : Thread) :
    let s' := (ArenaField.threads.alloc s x).1
    s'.core = s.core ∧ s'.tasks = s.tasks ∧ s'.waiting = s.waiting ∧
      s'.nestingDepth = s.nestingDepth ∧ s'.lockdown = s.lockdown :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end CStore

end Silmaril.Wasm.Component.Runtime
