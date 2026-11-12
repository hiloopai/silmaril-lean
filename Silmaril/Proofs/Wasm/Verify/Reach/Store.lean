module

public import Silmaril.Proofs.Wasm.Verify.Reach.Basic

/-!
# Function reachability: the store invariant under store updates

`StoreIn G` is preserved by every store update of the Core 3.0 step rules when the written
references are in `G`: global and table writes, element-segment drops, memory and data updates,
struct and array field writes, and allocation of structs, arrays and exceptions.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {H : Type} {G : Nat → Prop}

/-! ## Membership in updated lists -/

theorem mem_modify {α : Type} {l : List α} {i : Nat} {g : α → α} {y : α}
    (h : y ∈ l.modify i g) : ∃ x ∈ l, y = x ∨ y = g x := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  obtain ⟨x, hx, hy⟩ := getElem?_modify_some hj
  exact ⟨x, List.mem_of_getElem? hx, hy⟩

theorem mem_append_single {α : Type} {l : List α} {x y : α} (h : y ∈ l ++ [x]) :
    y ∈ l ∨ y = x := by
  simpa using h

/-! ## Updates -/

theorem StoreIn.setGlobal {s : Store H} (hs : StoreIn G s) {a : Nat} {v : Val}
    (hv : ∀ r, v = .ref r → RefIn G r) : StoreIn G (s.setGlobal a v) where
  globals g hg r hr := by
    obtain ⟨x, hx, rfl | rfl⟩ := mem_modify hg
    · exact hs.globals _ hx r hr
    · exact hv r hr
  tables := hs.tables
  elems := hs.elems
  structs := hs.structs
  arrays := hs.arrays
  exns := hs.exns

theorem StoreIn.setTable {s : Store H} (hs : StoreIn G s) {a : Nat} {ti : TableInst}
    (ht : ∀ r ∈ ti.refs, RefIn G r) : StoreIn G (s.setTable a ti) where
  globals := hs.globals
  tables t ht' r hr := by
    rcases List.mem_or_eq_of_mem_set ht' with ht' | rfl
    · exact hs.tables t ht' r hr
    · exact ht r hr
  elems := hs.elems
  structs := hs.structs
  arrays := hs.arrays
  exns := hs.exns

theorem StoreIn.setElemNil {s : Store H} (hs : StoreIn G s) {a : Nat} :
    StoreIn G (s.setElem a []) where
  globals := hs.globals
  tables := hs.tables
  elems e he r hr := by
    obtain ⟨x, hx, rfl | rfl⟩ := mem_modify he
    · exact hs.elems _ hx r hr
    · cases hr
  structs := hs.structs
  arrays := hs.arrays
  exns := hs.exns

theorem StoreIn.setMem {s : Store H} (hs : StoreIn G s) {a : Nat} {mi : MemInst} :
    StoreIn G (s.setMem a mi) :=
  ⟨hs.globals, hs.tables, hs.elems, hs.structs, hs.arrays, hs.exns⟩

theorem StoreIn.setData {s : Store H} (hs : StoreIn G s) {a : Nat} {b : ByteArray} :
    StoreIn G (s.setData a b) :=
  ⟨hs.globals, hs.tables, hs.elems, hs.structs, hs.arrays, hs.exns⟩

theorem StoreIn.setStructField {s : Store H} (hs : StoreIn G s) {a i : Nat} {fv : FieldVal}
    (hfv : ∀ r, fv = .val (.ref r) → RefIn G r) : StoreIn G (s.setStructField a i fv) where
  globals := hs.globals
  tables := hs.tables
  elems := hs.elems
  structs si hsi r hr := by
    obtain ⟨x, hx, rfl | rfl⟩ := mem_modify hsi
    · exact hs.structs _ hx r hr
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · exact hs.structs _ hx r hr
      · exact hfv r hr.symm
  arrays := hs.arrays
  exns := hs.exns

theorem StoreIn.setArrayField {s : Store H} (hs : StoreIn G s) {a i : Nat} {fv : FieldVal}
    (hfv : ∀ r, fv = .val (.ref r) → RefIn G r) : StoreIn G (s.setArrayField a i fv) where
  globals := hs.globals
  tables := hs.tables
  elems := hs.elems
  structs := hs.structs
  arrays ai hai r hr := by
    obtain ⟨x, hx, rfl | rfl⟩ := mem_modify hai
    · exact hs.arrays _ hx r hr
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · exact hs.arrays _ hx r hr
      · exact hfv r hr.symm
  exns := hs.exns

theorem StoreIn.addStruct {s : Store H} (hs : StoreIn G s) {si : StructInst}
    (hsi : ∀ r, FieldVal.val (.ref r) ∈ si.fields → RefIn G r) : StoreIn G (s.addStruct si) where
  globals := hs.globals
  tables := hs.tables
  elems := hs.elems
  structs x hx r hr := by
    rcases mem_append_single hx with hx | rfl
    · exact hs.structs x hx r hr
    · exact hsi r hr
  arrays := hs.arrays
  exns := hs.exns

theorem StoreIn.addArray {s : Store H} (hs : StoreIn G s) {ai : ArrayInst}
    (hai : ∀ r, FieldVal.val (.ref r) ∈ ai.fields → RefIn G r) : StoreIn G (s.addArray ai) where
  globals := hs.globals
  tables := hs.tables
  elems := hs.elems
  structs := hs.structs
  arrays x hx r hr := by
    rcases mem_append_single hx with hx | rfl
    · exact hs.arrays x hx r hr
    · exact hai r hr
  exns := hs.exns

theorem StoreIn.addExn {s : Store H} (hs : StoreIn G s) {e : ExnInst}
    (he : ∀ r, Val.ref r ∈ e.fields → RefIn G r) : StoreIn G (s.addExn e) where
  globals := hs.globals
  tables := hs.tables
  elems := hs.elems
  structs := hs.structs
  arrays := hs.arrays
  exns x hx r hr := by
    rcases mem_append_single hx with hx | rfl
    · exact hs.exns x hx r hr
    · exact he r hr

/-! ## Reads -/

theorem StoreIn.global {s : Store H} (hs : StoreIn G s) {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a, g)) {r : Ref} (hr : g.value = .ref r) :
    RefIn G r :=
  hs.globals g (List.mem_of_getElem? (Store.global?_spec' h).2) r hr

theorem StoreIn.table {s : Store H} (hs : StoreIn G s) {f : Frame} {x : TableIdx} {a : Nat}
    {ti : TableInst} (h : s.table? f x = some (a, ti)) {r : Ref} (hr : r ∈ ti.refs) : RefIn G r :=
  hs.tables ti (List.mem_of_getElem? (Store.table?_spec' h).2) r hr

theorem StoreIn.elem {s : Store H} (hs : StoreIn G s) {f : Frame} {x : ElemIdx} {a : Nat}
    {ei : ElemInst} (h : s.elem? f x = some (a, ei)) {r : Ref} (hr : r ∈ ei.refs) : RefIn G r :=
  hs.elems ei (List.mem_of_getElem? (Store.elem?_spec' h).2) r hr

theorem StoreIn.struct {s : Store H} (hs : StoreIn G s) {a : Nat} {si : StructInst}
    (h : s.structs[a]? = some si) {r : Ref} (hr : FieldVal.val (.ref r) ∈ si.fields) :
    RefIn G r :=
  hs.structs si (List.mem_of_getElem? h) r hr

theorem StoreIn.array {s : Store H} (hs : StoreIn G s) {a : Nat} {ai : ArrayInst}
    (h : s.arrays[a]? = some ai) {r : Ref} (hr : FieldVal.val (.ref r) ∈ ai.fields) :
    RefIn G r :=
  hs.arrays ai (List.mem_of_getElem? h) r hr

theorem StoreIn.exn {s : Store H} (hs : StoreIn G s) {a : Nat} {e : ExnInst}
    (h : s.exns[a]? = some e) {r : Ref} (hr : Val.ref r ∈ e.fields) : RefIn G r :=
  hs.exns e (List.mem_of_getElem? h) r hr

end Silmaril.Wasm.Verify
