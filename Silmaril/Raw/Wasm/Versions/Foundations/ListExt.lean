module

public import Init.Core

/-! # Index-stable list extension

`ListExt key l l'` says every entry of `l` survives in `l'` at the same index
with the same `key`: the shape of *store extension* in each Wasm subset
development, where `l` is the store's function instances and `key` their type,
so a step may allocate functions but never move or retype an existing one. The
two consequences the simulation proofs need are derived once: an allocated index
stays allocated, and any lookup reading only the `key` is stable.
-/

@[expose] public section

namespace Silmaril

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Every entry of `l` persists in `l'` at the same index with the same `key`. -/
def ListExt (key : α → β) (l l' : List α) : Prop :=
  ∀ (i : Nat) (x : α), l[i]? = some x → ∃ x', l'[i]? = some x' ∧ key x' = key x

/-- A list extends itself. -/
theorem ListExt.refl (key : α → β) (l : List α) : ListExt key l l :=
  fun _ x h => ⟨x, h, rfl⟩

/-- An allocated index stays allocated. -/
theorem ListExt.lt {key : α → β} {l l' : List α} (h : ListExt key l l') {i : Nat}
    (hi : i < l.length) : i < l'.length := by
  obtain ⟨x', h', -⟩ := h i l[i] (List.getElem?_eq_getElem hi)
  exact (List.getElem?_eq_some_iff.mp h').1

/-- A lookup reading only the `key` of an allocated entry is stable. -/
theorem ListExt.map_getElem? {key : α → β} {l l' : List α} (h : ListExt key l l')
    (g : β → γ) {i : Nat} (hi : i < l.length) :
    l'[i]?.map (fun x => g (key x)) = l[i]?.map (fun x => g (key x)) := by
  obtain ⟨x', h', ht⟩ := h i l[i] (List.getElem?_eq_getElem hi)
  simp [h', List.getElem?_eq_getElem hi, ht]

end Silmaril
