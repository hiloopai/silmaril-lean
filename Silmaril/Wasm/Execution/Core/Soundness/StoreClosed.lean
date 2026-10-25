module

public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-! # Closedness of struct/array instance types

Helper lemmas for the `StoreOk.structsClosed`/`StoreOk.arraysClosed` invariants
(a documented deviation from SpecTec §7.1 `Structinst_ok`/`Arrayinst_ok`, see
`Typing/Store.lean`): lookup, allocation (`Store.addStruct`/`Store.addArray`),
field updates, updates leaving `structs`/`arrays` untouched, extension, and the
closedness of module/frame types (the source of `struct.new`/`array.new*`
instance types).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Lookup -/

theorem StoreOk.struct_closed {s : Store H} (hs : StoreOk s) {a : Nat} {si : StructInst}
    (h : s.structs[a]? = some si) : TyOk {} si.type :=
  hs.structsClosed si (List.mem_of_getElem? h)

theorem StoreOk.array_closed {s : Store H} (hs : StoreOk s) {a : Nat} {ai : ArrayInst}
    (h : s.arrays[a]? = some ai) : TyOk {} ai.type :=
  hs.arraysClosed ai (List.mem_of_getElem? h)

/-! ## Generic list lemmas -/

theorem closed_append {α : Type} {P : α → Prop} {l : List α} {x : α}
    (hl : ∀ y ∈ l, P y) (hx : P x) : ∀ y ∈ l ++ [x], P y := by
  intro y hy
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · exact hl y hy
  · exact hx

theorem closed_modify {α β : Type} {P : β → Prop} {g : α → β} {l : List α} {a : Nat}
    {h : α → α} (hg : ∀ x, g (h x) = g x) (hl : ∀ y ∈ l, P (g y)) :
    ∀ y ∈ l.modify a h, P (g y) := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i < l.length := by simpa using hi
  by_cases hia : a = i
  · subst hia
    rw [List.getElem_modify_eq, hg]
    exact hl _ (List.getElem_mem hi')
  · rw [List.getElem_modify_ne _ _ hia]
    exact hl _ (List.getElem_mem hi')

/-! ## Allocation -/

theorem structsClosed_addStruct {s : Store H} {si : StructInst}
    (hs : ∀ x ∈ s.structs, TyOk {} x.type) (h : TyOk {} si.type) :
    ∀ x ∈ (s.addStruct si).structs, TyOk {} x.type :=
  closed_append hs h

theorem arraysClosed_addStruct {s : Store H} {si : StructInst}
    (hs : ∀ x ∈ s.arrays, TyOk {} x.type) :
    ∀ x ∈ (s.addStruct si).arrays, TyOk {} x.type := hs

theorem arraysClosed_addArray {s : Store H} {ai : ArrayInst}
    (hs : ∀ x ∈ s.arrays, TyOk {} x.type) (h : TyOk {} ai.type) :
    ∀ x ∈ (s.addArray ai).arrays, TyOk {} x.type :=
  closed_append hs h

theorem structsClosed_addArray {s : Store H} {ai : ArrayInst}
    (hs : ∀ x ∈ s.structs, TyOk {} x.type) :
    ∀ x ∈ (s.addArray ai).structs, TyOk {} x.type := hs

theorem structsClosed_addExn {s : Store H} {e : ExnInst}
    (hs : ∀ x ∈ s.structs, TyOk {} x.type) :
    ∀ x ∈ (s.addExn e).structs, TyOk {} x.type := hs

theorem arraysClosed_addExn {s : Store H} {e : ExnInst}
    (hs : ∀ x ∈ s.arrays, TyOk {} x.type) :
    ∀ x ∈ (s.addExn e).arrays, TyOk {} x.type := hs

/-! ## Field updates -/

theorem structsClosed_setStructField {s : Store H} {a i : Nat} {fv : FieldVal}
    (hs : ∀ x ∈ s.structs, TyOk {} x.type) :
    ∀ x ∈ (s.setStructField a i fv).structs, TyOk {} x.type :=
  closed_modify (g := StructInst.type) (fun _ => rfl) hs

theorem arraysClosed_setStructField {s : Store H} {a i : Nat} {fv : FieldVal}
    (hs : ∀ x ∈ s.arrays, TyOk {} x.type) :
    ∀ x ∈ (s.setStructField a i fv).arrays, TyOk {} x.type := hs

theorem arraysClosed_setArrayField {s : Store H} {a i : Nat} {fv : FieldVal}
    (hs : ∀ x ∈ s.arrays, TyOk {} x.type) :
    ∀ x ∈ (s.setArrayField a i fv).arrays, TyOk {} x.type :=
  closed_modify (g := ArrayInst.type) (fun _ => rfl) hs

theorem structsClosed_setArrayField {s : Store H} {a i : Nat} {fv : FieldVal}
    (hs : ∀ x ∈ s.structs, TyOk {} x.type) :
    ∀ x ∈ (s.setArrayField a i fv).structs, TyOk {} x.type := hs

/-! ## Updates leaving `structs`/`arrays` untouched, and extension -/

theorem structsClosed_of_eq {s s' : Store H} (heq : s'.structs = s.structs)
    (hs : StoreOk s) : ∀ x ∈ s'.structs, TyOk {} x.type := heq ▸ hs.structsClosed

theorem arraysClosed_of_eq {s s' : Store H} (heq : s'.arrays = s.arrays)
    (hs : StoreOk s) : ∀ x ∈ s'.arrays, TyOk {} x.type := heq ▸ hs.arraysClosed

/-- Closedness transfers along an extension, given closedness of the newly
allocated struct instances. -/
theorem structsClosed_extend {s s' : Store H} (hs : StoreOk s) (he : Extend s s')
    (hnew : ∀ (i : Nat) x, s.structs.length ≤ i → s'.structs[i]? = some x → TyOk {} x.type) :
    ∀ x ∈ s'.structs, TyOk {} x.type := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  by_cases hlt : i < s.structs.length
  · obtain ⟨y, hy, hxy⟩ := he.structs.2 i s.structs[i] (List.getElem?_eq_getElem hlt)
    rw [List.getElem?_eq_getElem hi] at hy
    cases hy
    rw [← hxy.1]
    exact hs.structsClosed _ (List.getElem_mem hlt)
  · exact hnew i _ (by omega) (List.getElem?_eq_getElem hi)

/-- Closedness transfers along an extension, given closedness of the newly
allocated array instances. -/
theorem arraysClosed_extend {s s' : Store H} (hs : StoreOk s) (he : Extend s s')
    (hnew : ∀ (i : Nat) x, s.arrays.length ≤ i → s'.arrays[i]? = some x → TyOk {} x.type) :
    ∀ x ∈ s'.arrays, TyOk {} x.type := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  by_cases hlt : i < s.arrays.length
  · obtain ⟨y, hy, hxy⟩ := he.arrays.2 i s.arrays[i] (List.getElem?_eq_getElem hlt)
    rw [List.getElem?_eq_getElem hi] at hy
    cases hy
    rw [← hxy.1]
    exact hs.arraysClosed _ (List.getElem_mem hlt)
  · exact hnew i _ (by omega) (List.getElem?_eq_getElem hi)

/-! ## Closedness of module and frame types -/

theorem ModuleInstOk.type_closed {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : Nat} {d : DefType} (hx : mi.types[x]? = some d) :
    TyOk {} d := by
  cases h with
  | mk htypes => exact htypes d (List.mem_of_getElem? hx)

theorem FrameOk.type_closed {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : Nat} {d : DefType} (hx : f.module.types[x]? = some d) : TyOk {} d := by
  obtain ⟨_, _, hm, _, _⟩ := h
  exact hm.type_closed hx

theorem StateOk.frameType_closed {s : Store H} {f : Frame} {C : Context} (h : StateOk s f C)
    {x : Nat} {d : DefType} (hx : f.module.types[x]? = some d) : TyOk {} d :=
  h.2.type_closed hx

end Silmaril.Wasm.Execution.Core
