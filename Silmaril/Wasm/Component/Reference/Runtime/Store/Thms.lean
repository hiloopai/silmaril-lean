module

public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Objects.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms

/-!
# `Runtime.Store`: laws of the component reference

Theorems of the component reference copy `Runtime.Store`, refined out of
`Silmaril.Raw.Wasm.Component.Runtime.Store`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

namespace ArenaField

variable {E : CoreEngine} {Id α : Type} (F : ArenaField E Id α)

/-- Allocation adds exactly the fresh id and leaves every other lookup unchanged. -/
theorem get?_alloc (s : CStore E) (x : α) (i : Id) :
    F.get? (F.alloc s x).1 i = if F.idx i = F.size s then some x else F.get? s i := by
  simp only [alloc, get?, get_put, size, Arena.alloc, Arena.get?_eq_getElem?]
  by_cases h : F.idx i = (F.get s).length
  · simp [h]
  · simp only [h, ite_false]
    rcases Nat.lt_or_gt_of_ne h with h | h
    · simp [List.getElem?_append_left h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem get?_isSome_iff (s : CStore E) (i : Id) : (F.get? s i).isSome ↔ F.idx i < F.size s :=
  Arena.get?_isSome_iff ..

section DecEq

variable [DecidableEq Id]

theorem get?_set (s : CStore E) (i j : Id) (x : α) :
    F.get? (F.set s i x) j = if i = j then (F.get? s j).map (fun _ => x) else F.get? s j := by
  simp only [set, get?, get_put, Arena.set, Arena.get?_eq_getElem?, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : F.idx i < (F.get s).length
    · simp [hl]
    · simp [hl]
  · have : F.idx i ≠ F.idx j := fun e => h (F.idx_injective e)
    simp [h, this]

end DecEq

end ArenaField

end Silmaril.Wasm.Component.Runtime
