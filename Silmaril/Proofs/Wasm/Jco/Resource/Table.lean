module

public import Silmaril.Wasm.Jco.Resource.Basic.Defs
public import Silmaril.Wasm.Resource.Table.Thms

/-!
# The canonical handle tables are a lawful handle-table implementation

`refTab_lawful`: the reference machine's `Table` (`definitions.py` class `Table`), with capacity
`|free| + (MAX_LENGTH + 1 - |array|)` and invariant `FreeOK` plus `|array| ≤ MAX_LENGTH + 1`,
satisfies `HTab.Lawful`. Freshness and framing are `add?_fresh` and `remove?_live` of
`Silmaril.Wasm.Resource.Table`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Resource (FreeOK AddRes RemoveRes add?_fresh remove?_live)
open Silmaril.Wasm.Component.Runtime (Table)

/-- What `add?` does to the array size and the free stack. -/
theorem add?_shape {t t' : Table HEntry} {e : HEntry} {i : Nat} (h : t.add? e = some (i, t')) :
    (∃ fr, t.free = i :: fr ∧ t'.free = fr ∧ t'.array.size = t.array.size) ∨
      (t.free = [] ∧ t'.free = [] ∧ t.array.size ≤ Table.maxLength ∧ i = t.array.size ∧
        t'.array.size = t.array.size + 1) := by
  rcases t with ⟨arr, _ | ⟨k, fr⟩⟩
  · by_cases hs : arr.size ≤ Table.maxLength
    · have he : (arr.size, (⟨arr.push (some e), []⟩ : Table HEntry)) = (i, t') := by
        simpa [Table.add?, hs] using h
      rw [← (Prod.mk.inj he).1, ← (Prod.mk.inj he).2]
      exact .inr ⟨rfl, rfl, hs, rfl, by simp⟩
    · simp [Table.add?, hs] at h
  · have he : (k, (⟨arr.setIfInBounds k (some e), fr⟩ : Table HEntry)) = (i, t') := by
      simpa [Table.add?] using h
    rw [← (Prod.mk.inj he).1, ← (Prod.mk.inj he).2]
    exact .inl ⟨fr, rfl, rfl, by simp⟩

theorem lt_size_of_get? {t : Table HEntry} {i : Nat} {e : HEntry} (h : t.get? i = some e) :
    i < t.array.size := by
  by_contra hc
  have hn : t.array[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hc)
  simp [Table.get?, hn] at h

theorem refTab_add_some (t : Table HEntry) (e : HEntry) (hc : refTab.cap t ≠ some 0) :
    (refTab.add? t e).isSome := by
  rcases t with ⟨arr, _ | ⟨k, fr⟩⟩
  · have hs : arr.size ≤ Table.maxLength := by
      by_contra hn
      exact hc (by simp [refTab]; omega)
    simp [refTab, Table.add?, hs]
  · simp [refTab, Table.add?]

theorem refTab_add_spec (t : Table HEntry) (e : HEntry) (i : Nat) (t' : Table HEntry)
    (hI : refTab.Inv t) (h : refTab.add? t e = some (i, t')) :
    i < 2 ^ 32 ∧ refTab.get? t i = none ∧ refTab.get? t' i = some e ∧
      (∀ j, j ≠ i → refTab.get? t' j = refTab.get? t j) ∧ refTab.Inv t' ∧
        refTab.cap t' = (refTab.cap t).map (· - 1) := by
  have hr : AddRes t t' e i := add?_fresh hI.1 h
  have hsz0 : t.array.size ≤ Table.maxLength + 1 := hI.2
  have hsz : t'.array.size ≤ Table.maxLength + 1 := by
    rcases add?_shape h with ⟨fr, _, _, hs⟩ | ⟨_, _, hle, _, hs⟩ <;> omega
  have hi : i < t'.array.size := lt_size_of_get? hr.2.1
  have hcap : refTab.cap t' = (refTab.cap t).map (· - 1) := by
    rcases add?_shape h with ⟨fr, hf, hf', hs⟩ | ⟨hf, hf', hle, _, hs⟩
    · simp only [refTab, Option.map_some, hf, hf', hs, List.length_cons, Option.some.injEq]
      omega
    · simp only [refTab, Option.map_some, hf, hf', hs, List.length_nil, Option.some.injEq]
      omega
  have h32 : i < 2 ^ 32 := by
    have hm : Table.maxLength + 1 ≤ 2 ^ 32 := by simp [Table.maxLength]
    omega
  exact ⟨h32, hr.1, hr.2.1, hr.2.2.1, ⟨hr.2.2.2, hsz⟩, hcap⟩

theorem refTab_remove_some (t : Table HEntry) (i : Nat) (e : HEntry)
    (h : refTab.get? t i = some e) : ∃ t', refTab.remove? t i = some (e, t') :=
  ⟨⟨t.array.setIfInBounds i none, i :: t.free⟩,
    by simp [refTab, Table.remove?, show t.get? i = some e from h]⟩

theorem refTab_remove_spec (t : Table HEntry) (i : Nat) (e : HEntry) (t' : Table HEntry)
    (hI : refTab.Inv t) (h : refTab.remove? t i = some (e, t')) :
    refTab.get? t i = some e ∧ refTab.get? t' i = none ∧
      (∀ j, j ≠ i → refTab.get? t' j = refTab.get? t j) ∧ refTab.Inv t' ∧
        refTab.cap t' = (refTab.cap t).map (· + 1) := by
  have hr : RemoveRes t t' e i := remove?_live hI.1 h
  have ht' : t' = ⟨t.array.setIfInBounds i none, i :: t.free⟩ := by
    have hm : (t.get? i).map (fun e => (e, (⟨t.array.setIfInBounds i none, i :: t.free⟩ :
        Table HEntry))) = some (e, t') := h
    rw [hr.1] at hm
    exact (Prod.mk.inj (Option.some.inj hm)).2.symm
  have hs : t'.array.size = t.array.size := by rw [ht']; simp
  have hf : t'.free.length = t.free.length + 1 := by rw [ht']; simp
  have hcap : refTab.cap t' = (refTab.cap t).map (· + 1) := by
    simp only [refTab, Option.map_some, hs, hf, Option.some.injEq]
    omega
  exact ⟨hr.1, hr.2.1, hr.2.2.1, ⟨hr.2.2.2, hs ▸ hI.2⟩, hcap⟩

/-- **The canonical handle tables are lawful.** -/
theorem refTab_lawful : refTab.Lawful where
  add_some t e _ hc := refTab_add_some t e hc
  add_spec := refTab_add_spec
  touch_spec _ _ _ hI _ := ⟨fun _ => rfl, rfl, hI⟩
  remove_some := refTab_remove_some
  remove_spec := refTab_remove_spec

end Silmaril.Proofs.Wasm.Jco.Res
