module

public import Silmaril.Wasm.Logic.Iris.Heap.Defs
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# The cells of a store after an instruction's update

For each store update of the state instructions (`Store.setGlobal`,
`Store.setMem`, `Store.setTable`, `Store.setStructField`, `Store.setArrayField`,
`Store.addStruct`, `Store.addArray`, a new frame), which cells change and which
are kept. These discharge the side conditions of `interp_change`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (Region bytesAt getElem?_bytesAt)

variable {H : Type}

/-! ## Indexed cells -/

theorem mem_idxCells {α : Type} {loc : Nat → ILoc} {cell : α → ICell} :
    ∀ {i : Nat} {xs : List α} {p : ILoc × ICell}, p ∈ idxCells loc cell i xs ↔
      ∃ (k : Nat) (h : k < xs.length), p = (loc (i + k), cell xs[k])
  | _, [], _ => by simp [idxCells]
  | i, x :: xs, p => by
    simp only [idxCells, List.mem_cons, mem_idxCells, List.length_cons]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨k + 1, by omega, by simp [Nat.add_assoc, Nat.add_comm 1 k]⟩
    · rintro ⟨k, hk, rfl⟩
      rcases k with _ | k
      · exact .inl (by simp)
      · exact .inr ⟨k, by omega, by simp [Nat.add_assoc, Nat.add_comm 1 k]⟩

theorem fst_idxCells {α : Type} (loc : Nat → ILoc) (cell : α → ICell) :
    ∀ (i : Nat) (xs : List α), (idxCells loc cell i xs).map Prod.fst =
      (List.range' i xs.length).map loc
  | _, [] => rfl
  | i, x :: xs => by
    simp [idxCells, fst_idxCells loc cell (i + 1) xs, List.range'_succ]

theorem nodup_idxCells {α : Type} {loc : Nat → ILoc} {cell : α → ICell}
    (hl : Function.Injective loc) (i : Nat) (xs : List α) :
    ((idxCells loc cell i xs).map Prod.fst).Nodup := by
  rw [fst_idxCells]
  exact (List.nodup_range' ..).map hl

theorem idxCells_fst_eq {α β : Type} (loc : Nat → ILoc) (cell : α → ICell) (cell' : β → ICell)
    (i : Nat) {xs : List α} {ys : List β} (h : xs.length = ys.length) :
    (idxCells loc cell i xs).map Prod.fst = (idxCells loc cell' i ys).map Prod.fst := by
  rw [fst_idxCells, fst_idxCells, h]

/-! ## Bytes -/

theorem byteArray_getElem? (B : ByteArray) (i : Nat) : B[i]? = B.data.toList[i]? := by
  rw [Array.getElem?_toList]
  rfl

theorem cellOf_byte {s : Store H} {f : Frame} {m i : Nat} {b : UInt8} :
    cellOf s f (.byte m i) = some (.byte b) ↔
      ∃ mi, s.mems[m]? = some mi ∧ mi.bytes.data.toList[i]? = some b := by
  rcases hm : s.mems[m]? with _ | mi <;> simp [cellOf, hm, byteArray_getElem?]

/-- Owned bytes are the bytes of the memory. -/
theorem bytes_of_cells {s : Store H} {f : Frame} {ma a : Nat} {bs : List UInt8} (hne : bs ≠ [])
    (h : ∀ p ∈ idxCells (.byte ma) .byte a bs, cellOf s f p.1 = some p.2) :
    ∃ mi, s.mems[ma]? = some mi ∧ a + bs.length ≤ mi.bytes.size ∧
      bytesAt mi.bytes ⟨a, bs.length⟩ = bs := by
  have hb : ∀ k (hk : k < bs.length), ∃ mi, s.mems[ma]? = some mi ∧
      mi.bytes.data.toList[a + k]? = some bs[k] :=
    fun k hk => cellOf_byte.mp (h _ (mem_idxCells.mpr ⟨k, hk, rfl⟩))
  obtain ⟨mi, hmi, -⟩ := hb 0 (List.length_pos_iff.mpr hne)
  have hk : ∀ k (hk : k < bs.length), mi.bytes.data.toList[a + k]? = some bs[k] := fun k hk => by
    obtain ⟨mi', hmi', hb'⟩ := hb k hk
    have hmm : mi' = mi := Option.some.inj (hmi'.symm.trans hmi)
    exact hmm ▸ hb'
  refine ⟨mi, hmi, ?_, ?_⟩
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hne
    have hlast : mi.bytes.data.toList[a + (bs.length - 1)]? = some bs[bs.length - 1] :=
      hk (bs.length - 1) (by omega)
    have hlt : a + (bs.length - 1) < mi.bytes.size := by
      simpa using (List.getElem?_eq_some_iff.mp hlast).1
    omega
  · apply List.ext_getElem?
    intro k
    rw [getElem?_bytesAt]
    by_cases hkl : k < bs.length
    · simp only [hkl, ↓reduceIte, hk k hkl, List.getElem?_eq_getElem hkl]
    · simp [hkl]

/-! ## Updates -/

theorem cellOf_frame_ne {s : Store H} {f f' : Frame} {l : ILoc} (h : l ≠ .frame) :
    cellOf s f' l = cellOf s f l := by
  cases l <;> first | exact absurd rfl h | rfl

theorem cellOf_setGlobal_self {s : Store H} {f : Frame} {a : Nat} {v : Val}
    (ha : a < s.globals.length) : cellOf (s.setGlobal a v) f (.global a) = some (.val v) := by
  simp [cellOf, Store.setGlobal, ha]

theorem cellOf_setGlobal_ne {s : Store H} {f : Frame} {a : Nat} {v : Val} {l : ILoc}
    (h : l ≠ .global a) : cellOf (s.setGlobal a v) f l = cellOf s f l := by
  cases l with
  | global b =>
    have hb : a ≠ b := fun he => h (by rw [he])
    simp [cellOf, Store.setGlobal, hb]
  | _ => rfl

theorem cellOf_setTable_self {s : Store H} {f : Frame} {t i : Nat} {ti : TableInst} {r : Ref}
    (ht : s.tables[t]? = some ti) (hi : i < ti.refs.length) :
    cellOf (s.setTable t { ti with refs := ti.refs.set i r }) f (.tableElem t i) =
      some (.ref r) := by
  have htl : t < s.tables.length := (List.getElem?_eq_some_iff.mp ht).1
  simp [cellOf, Store.setTable, htl, hi]

theorem cellOf_setTable_ne {s : Store H} {f : Frame} {t i : Nat} {ti : TableInst} {r : Ref}
    {l : ILoc} (ht : s.tables[t]? = some ti) (h : l ≠ .tableElem t i) :
    cellOf (s.setTable t { ti with refs := ti.refs.set i r }) f l = cellOf s f l := by
  cases l with
  | tableElem t' j =>
    by_cases htt : t = t'
    · subst htt
      have hij : i ≠ j := fun he => h (by rw [he])
      obtain ⟨htl, hti⟩ := List.getElem?_eq_some_iff.mp ht
      simp [cellOf, Store.setTable, htl, hti, hij]
    · simp [cellOf, Store.setTable, htt]
  | _ => rfl

theorem cellOf_setStructField_self {s : Store H} {f : Frame} {a i : Nat} {si : StructInst}
    {fv : FieldVal} (hs : s.structs[a]? = some si) (hi : i < si.fields.length) :
    cellOf (s.setStructField a i fv) f (.field a i) = some (.field fv) := by
  simp [cellOf, Store.setStructField, hs, hi]

theorem cellOf_setStructField_ne {s : Store H} {f : Frame} {a i : Nat} {fv : FieldVal}
    {l : ILoc} (h : l ≠ .field a i) :
    cellOf (s.setStructField a i fv) f l = cellOf s f l := by
  cases l with
  | field b j =>
    by_cases hab : a = b
    · subst hab
      have hij : i ≠ j := fun he => h (by rw [he])
      rcases hs : s.structs[a]? with _ | si <;>
        simp [cellOf, Store.setStructField, hs, hij]
    · simp [cellOf, Store.setStructField, hab]
  | _ => rfl

theorem cellOf_setArrayField_self {s : Store H} {f : Frame} {a i : Nat} {ai : ArrayInst}
    {fv : FieldVal} (ha : s.arrays[a]? = some ai) (hi : i < ai.fields.length) :
    cellOf (s.setArrayField a i fv) f (.elem a i) = some (.field fv) := by
  simp [cellOf, Store.setArrayField, ha, hi]

theorem cellOf_setArrayField_ne {s : Store H} {f : Frame} {a i : Nat} {fv : FieldVal}
    {l : ILoc} (h : l ≠ .elem a i) :
    cellOf (s.setArrayField a i fv) f l = cellOf s f l := by
  cases l with
  | elem b j =>
    by_cases hab : a = b
    · subst hab
      have hij : i ≠ j := fun he => h (by rw [he])
      rcases ha : s.arrays[a]? with _ | ai <;>
        simp [cellOf, Store.setArrayField, ha, hij]
    · simp [cellOf, Store.setArrayField, hab]
  | arrLen b =>
    by_cases hab : a = b
    · subst hab
      rcases ha : s.arrays[a]? with _ | ai <;>
        simp [cellOf, Store.setArrayField, ha]
    · simp [cellOf, Store.setArrayField, hab]
  | _ => rfl

theorem cellOf_addStruct_old {s : Store H} {f : Frame} {si : StructInst} {l : ILoc} {c : ICell}
    (h : cellOf s f l = some c) : cellOf (s.addStruct si) f l = some c := by
  cases l with
  | field a i =>
    rcases hs : s.structs[a]? with _ | si'
    · simp [cellOf, hs] at h
    · have ha : a < s.structs.length := (List.getElem?_eq_some_iff.mp hs).1
      simpa [cellOf, Store.addStruct, List.getElem?_append_left ha] using h
  | _ => exact h

theorem cellOf_addStruct_new {s : Store H} {f : Frame} {si : StructInst} {i : Nat}
    {fv : FieldVal} (h : si.fields[i]? = some fv) :
    cellOf (s.addStruct si) f (.field s.structs.length i) = some (.field fv) := by
  simp [cellOf, Store.addStruct, h]

theorem cellOf_field_fresh {s : Store H} {f : Frame} (i : Nat) :
    cellOf s f (.field s.structs.length i) = none := by
  simp [cellOf]

theorem cellOf_addArray_old {s : Store H} {f : Frame} {ai : ArrayInst} {l : ILoc} {c : ICell}
    (h : cellOf s f l = some c) : cellOf (s.addArray ai) f l = some c := by
  cases l with
  | elem a i =>
    rcases hs : s.arrays[a]? with _ | ai'
    · simp [cellOf, hs] at h
    · have ha : a < s.arrays.length := (List.getElem?_eq_some_iff.mp hs).1
      simpa [cellOf, Store.addArray, List.getElem?_append_left ha] using h
  | arrLen a =>
    rcases hs : s.arrays[a]? with _ | ai'
    · simp [cellOf, hs] at h
    · have ha : a < s.arrays.length := (List.getElem?_eq_some_iff.mp hs).1
      simpa [cellOf, Store.addArray, List.getElem?_append_left ha] using h
  | _ => exact h

theorem cellOf_addArray_elem {s : Store H} {f : Frame} {ai : ArrayInst} {i : Nat}
    {fv : FieldVal} (h : ai.fields[i]? = some fv) :
    cellOf (s.addArray ai) f (.elem s.arrays.length i) = some (.field fv) := by
  simp [cellOf, Store.addArray, h]

theorem cellOf_addArray_len {s : Store H} {f : Frame} {ai : ArrayInst} :
    cellOf (s.addArray ai) f (.arrLen s.arrays.length) = some (.len ai.fields.length) := by
  simp [cellOf, Store.addArray]

theorem cellOf_array_fresh {s : Store H} {f : Frame} {l : ILoc}
    (h : l = .arrLen s.arrays.length ∨ ∃ i, l = .elem s.arrays.length i) :
    cellOf s f l = none := by
  rcases h with rfl | ⟨i, rfl⟩ <;> simp [cellOf]

theorem cellOf_setMem_byte {s : Store H} {f : Frame} {ma j : Nat} {mi mi' : MemInst}
    (hm : s.mems[ma]? = some mi) :
    cellOf (s.setMem ma mi') f (.byte ma j) = (mi'.bytes.data.toList[j]?).map .byte := by
  have hl : ma < s.mems.length := (List.getElem?_eq_some_iff.mp hm).1
  simp [cellOf, Store.setMem, hl, byteArray_getElem?]

theorem cellOf_setMem_mem {s : Store H} {f : Frame} {ma : Nat} {mi mi' : MemInst}
    (hm : s.mems[ma]? = some mi) :
    cellOf (s.setMem ma mi') f (.mem ma) = some (.mem mi'.type mi'.bytes.size) := by
  have hl : ma < s.mems.length := (List.getElem?_eq_some_iff.mp hm).1
  simp [cellOf, Store.setMem, hl]

theorem cellOf_setMem_other {s : Store H} {f : Frame} {ma : Nat} {mi' : MemInst} {l : ILoc}
    (h₁ : ∀ j, l ≠ .byte ma j) (h₂ : l ≠ .mem ma) :
    cellOf (s.setMem ma mi') f l = cellOf s f l := by
  cases l with
  | byte m j =>
    have hm : ma ≠ m := fun he => h₁ j (by rw [he])
    simp [cellOf, Store.setMem, hm]
  | mem m =>
    have hm : ma ≠ m := fun he => h₂ (by rw [he])
    simp [cellOf, Store.setMem, hm]
  | _ => rfl

theorem cellOf_mem {s : Store H} {f : Frame} {m : Nat} {t : MemoryType} {sz : Nat} :
    cellOf s f (.mem m) = some (.mem t sz) ↔
      ∃ mi, s.mems[m]? = some mi ∧ mi.type = t ∧ mi.bytes.size = sz := by
  rcases hm : s.mems[m]? with _ | mi <;> simp [cellOf, hm]

end Silmaril.Wasm.Logic.IrisWasm
