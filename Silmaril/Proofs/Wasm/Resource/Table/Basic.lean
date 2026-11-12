module

public import Silmaril.Wasm.Resource.Table.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# Handle tables of the component reference machine: proofs

* `add?_fresh`, `remove?_live`: `Table.add?` returns an index that was empty and fills only it;
  `Table.remove?` empties only an index that was valid; both keep `FreeOK`.
* `tabRel_step`: one successful table event is accepted by the handle protocol, in either
  orientation, from a state related to the table, and the relation is kept.
* `table_steps_run`, `table_steps_accepts`: every successful history from `Table.empty` is
  accepted by `handleProto ℕ r`, for both roles `r`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component.Runtime

variable {α : Type}

theorem freeOK_empty : FreeOK (Table.empty : Silmaril.Wasm.Component.Runtime.Table α) :=
  ⟨fun _ h => by simp [Table.empty] at h, List.nodup_nil⟩

theorem tabRel_empty : TabRel [] (Table.empty : Silmaril.Wasm.Component.Runtime.Table α) := by
  refine ⟨List.nodup_nil, fun i => ?_⟩
  cases i <;> simp [Table.empty, Table.get?]

/-- What a successful `add?` does: index `i` was empty and now holds `e`, the other indices are
unchanged, and `FreeOK` is kept. -/
def AddRes (t t' : Silmaril.Wasm.Component.Runtime.Table α) (e : α) (i : ℕ) : Prop :=
  t.get? i = none ∧ t'.get? i = some e ∧ (∀ j, j ≠ i → t'.get? j = t.get? j) ∧ FreeOK t'

/-- What a successful `remove?` does: index `i` held `e` and is now empty, the other indices are
unchanged, and `FreeOK` is kept. -/
def RemoveRes (t t' : Silmaril.Wasm.Component.Runtime.Table α) (e : α) (i : ℕ) : Prop :=
  t.get? i = some e ∧ t'.get? i = none ∧ (∀ j, j ≠ i → t'.get? j = t.get? j) ∧ FreeOK t'

theorem lt_of_getElem?_eq_some {β : Type} {arr : Array β} {k : ℕ} {x : β}
    (h : arr[k]? = some x) : k < arr.size := by
  by_contra hc
  simp [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h

theorem add?_fresh_cons {arr : Array (Option α)} {k : ℕ} {fr : List ℕ} {e : α}
    (hf : FreeOK (⟨arr, k :: fr⟩ : Silmaril.Wasm.Component.Runtime.Table α)) :
    AddRes ⟨arr, k :: fr⟩ ⟨arr.setIfInBounds k (some e), fr⟩ e k := by
  have hk : arr[k]? = some none := hf.1 k (by simp)
  have hlt : k < arr.size := lt_of_getElem?_eq_some hk
  have hnd : k ∉ fr ∧ fr.Nodup := List.nodup_cons.1 hf.2
  have hfr : ∀ j ∈ fr, (arr.setIfInBounds k (some e))[j]? = some none := fun j hj => by
    have hjk : k ≠ j := fun hkj => hnd.1 (hkj ▸ hj)
    simpa [Array.getElem?_setIfInBounds_ne hjk] using hf.1 j (by simp [hj])
  refine ⟨by simp [Table.get?, hk], by simp [Table.get?, hlt], fun j hj => ?_, hfr, hnd.2⟩
  simp [Table.get?, Array.getElem?_setIfInBounds_ne (Ne.symm hj)]

theorem add?_fresh_push {arr : Array (Option α)} {e : α} :
    AddRes ⟨arr, []⟩ ⟨arr.push (some e), []⟩ e arr.size := by
  refine ⟨by simp [Table.get?], by simp [Table.get?], fun j hj => ?_,
    ⟨fun _ hj => by simp at hj, List.nodup_nil⟩⟩
  simp [Table.get?, Array.getElem?_push, hj]

/-- **`add?` returns a fresh index.** -/
theorem add?_fresh {t t' : Silmaril.Wasm.Component.Runtime.Table α} {e : α} {i : ℕ} (hf : FreeOK t)
    (h : t.add? e = some (i, t')) : AddRes t t' e i := by
  obtain ⟨arr, fr⟩ := t
  cases fr with
  | cons k fr =>
    have h' : k = i ∧ (⟨arr.setIfInBounds k (some e), fr⟩ : Silmaril.Wasm.Component.Runtime.Table α) = t' := by
      simpa [Table.add?] using h
    obtain ⟨rfl, rfl⟩ := h'
    exact add?_fresh_cons hf
  | nil =>
    have h' : arr.size = i ∧ (⟨arr.push (some e), []⟩ : Silmaril.Wasm.Component.Runtime.Table α) = t' := by
      simp only [Table.add?] at h
      split at h <;> simp_all
    obtain ⟨rfl, rfl⟩ := h'
    exact add?_fresh_push

theorem remove?_parts {t t' : Silmaril.Wasm.Component.Runtime.Table α} {e : α} {i : ℕ} (h : t.remove? i = some (e, t')) :
    t.get? i = some e ∧ t' = ⟨t.array.setIfInBounds i none, i :: t.free⟩ := by
  obtain ⟨e', he', hp⟩ := Option.map_eq_some_iff.1 h
  have hp' : e' = e ∧ (⟨t.array.setIfInBounds i none, i :: t.free⟩ : Silmaril.Wasm.Component.Runtime.Table α) = t' := by
    simpa only [Prod.mk.injEq] using hp
  exact ⟨hp'.1 ▸ he', hp'.2.symm⟩

theorem getElem?_of_get? {arr : Array (Option α)} {fr : List ℕ} {i : ℕ} {e : α}
    (h : (⟨arr, fr⟩ : Silmaril.Wasm.Component.Runtime.Table α).get? i = some e) : arr[i]? = some (some e) := by
  simp only [Table.get?] at h
  cases hai : arr[i]? with
  | none => simp [hai] at h
  | some o => cases o <;> simp_all

/-- **`remove?` succeeds only on a valid index.** -/
theorem remove?_live {t t' : Silmaril.Wasm.Component.Runtime.Table α} {e : α} {i : ℕ} (hf : FreeOK t)
    (h : t.remove? i = some (e, t')) : RemoveRes t t' e i := by
  obtain ⟨he, rfl⟩ := remove?_parts h
  obtain ⟨arr, fr⟩ := t
  have hi : arr[i]? = some (some e) := getElem?_of_get? he
  have hlt : i < arr.size := lt_of_getElem?_eq_some hi
  have hni : i ∉ fr := fun hm => by simp [hf.1 i hm] at hi
  have hfr : ∀ j ∈ i :: fr, (arr.setIfInBounds i none)[j]? = some none := fun j hj => by
    rcases List.mem_cons.1 hj with rfl | hj
    · simp [hlt]
    · have hij : i ≠ j := fun hij => hni (hij ▸ hj)
      simpa [Array.getElem?_setIfInBounds_ne hij] using hf.1 j hj
  refine ⟨he, by simp [Table.get?, hlt], fun j hj => ?_, hfr, List.nodup_cons.2 ⟨hni, hf.2⟩⟩
  simp [Table.get?, Array.getElem?_setIfInBounds_ne (Ne.symm hj)]

theorem tabRel_alloc {t t' : Silmaril.Wasm.Component.Runtime.Table α} {e : α} {i : ℕ} (hr : AddRes t t' e i) {L : List ℕ}
    (hL : TabRel L t) (r : Role) :
    handleStep r (some L) (.alloc i) = some (some (i :: L)) ∧ TabRel (i :: L) t' := by
  obtain ⟨hfresh, hnew, hframe, -⟩ := hr
  have hiL : i ∉ L := fun h => by
    have h' := (hL.2 i).1 h
    rw [hfresh] at h'
    cases h'
  refine ⟨by simp [handleStep, hiL], List.nodup_cons.2 ⟨hiL, hL.1⟩, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    simp [hnew]
  · simp [hj, hframe j hj, hL.2 j]

theorem tabRel_free {t t' : Silmaril.Wasm.Component.Runtime.Table α} {e : α} {i : ℕ} (hr : RemoveRes t t' e i) {L : List ℕ}
    (hL : TabRel L t) (r : Role) :
    handleStep r (some L) (.free i) = some (some (L.erase i)) ∧ TabRel (L.erase i) t' := by
  obtain ⟨hlive, hgone, hframe, -⟩ := hr
  have hiL : i ∈ L := (hL.2 i).2 (by simp [hlive])
  refine ⟨by simp [handleStep, hiL], hL.1.erase i, fun j => ?_⟩
  rw [hL.1.mem_erase_iff]
  by_cases hj : j = i
  · subst hj
    simp [hgone]
  · simp [hj, hframe j hj, hL.2 j]

theorem tabRel_use {t : Silmaril.Wasm.Component.Runtime.Table α} {e : α} {i : ℕ} (hg : t.get? i = some e) {L : List ℕ}
    (hL : TabRel L t) (r : Role) : handleStep r (some L) (.use i) = some (some L) := by
  have hiL : i ∈ L := (hL.2 i).2 (by simp [hg])
  simp [handleStep, hiL]

/-- **One successful table event is accepted** by the handle protocol in either orientation, and
the relation to the table is kept. -/
theorem tabRel_step {t t' : Silmaril.Wasm.Component.Runtime.Table α} {ev : Table.Event α} (hs : t.step? ev.op = some (ev, t'))
    (hf : FreeOK t) {L : List ℕ} (hL : TabRel L t) (r : Role) :
    ∃ L', handleStep r (some L) (tableEv ev) = some (some L') ∧ TabRel L' t' ∧ FreeOK t' := by
  cases ev with
  | added i e =>
    obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 hs
    have hp' : t.add? e = some (i, t') := by
      obtain ⟨p1, p2⟩ := p
      simp only [Prod.mk.injEq, Table.Event.added.injEq] at hpe
      rw [hp, ← hpe.1.1, ← hpe.2]
    have hr : AddRes t t' e i := add?_fresh hf hp'
    exact ⟨i :: L, (tabRel_alloc hr hL r).1, (tabRel_alloc hr hL r).2, hr.2.2.2⟩
  | got i e =>
    obtain ⟨e', he', hpe⟩ := Option.map_eq_some_iff.1 hs
    injection hpe with _ ht
    subst ht
    exact ⟨L, tabRel_use he' hL r, hL, hf⟩
  | removed i e =>
    obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 hs
    have hp' : t.remove? i = some (p.1, t') := by
      rw [hp, ← (Prod.mk.inj hpe).2]
    have hr : RemoveRes t t' p.1 i := remove?_live hf hp'
    exact ⟨L.erase i, (tabRel_free hr hL r).1, (tabRel_free hr hL r).2, hr.2.2.2⟩

/-- **Every successful table history is accepted** from a related state, in either
orientation. -/
theorem table_steps_run {t t' : Silmaril.Wasm.Component.Runtime.Table α} {evs : List (Table.Event α)} (h : Table.Steps t evs t')
    (r : Role) :
    ∀ {L : List ℕ}, FreeOK t → TabRel L t →
      ∃ L', (handleProto ℕ r).run (some L) (evs.map tableEv) = some (some L') ∧ TabRel L' t' ∧
        FreeOK t' := by
  induction h with
  | nil t => exact fun hf hL => ⟨_, rfl, hL, hf⟩
  | cons hs _ ih =>
    intro L hf hL
    obtain ⟨L₁, h₁, hL₁, hf₁⟩ := tabRel_step hs hf hL r
    obtain ⟨L₂, h₂, hL₂, hf₂⟩ := ih hf₁ hL₁
    refine ⟨L₂, ?_, hL₂, hf₂⟩
    rw [List.map_cons, Protocol.run_cons]
    change (handleStep r (some L) (tableEv _)).bind _ = _
    rw [h₁]
    exact h₂

/-- **The reference machine's handle tables respect the handle protocol**: every successful
history from the empty table is accepted by `handleProto ℕ r`, for both roles. -/
theorem table_steps_accepts {t' : Silmaril.Wasm.Component.Runtime.Table α} {evs : List (Table.Event α)}
    (h : Table.Steps Table.empty evs t') (r : Role) :
    (handleProto ℕ r).Accepts (evs.map tableEv) := by
  obtain ⟨L, hL, -⟩ := table_steps_run h r freeOK_empty tabRel_empty
  show ((handleProto ℕ r).run (some []) _).isSome
  rw [hL]
  rfl

end Silmaril.Wasm.Resource
