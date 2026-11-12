module

public import Silmaril.Proofs.Wasm.Logic.Sep.GC
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# Separation logic over the Core 3.0 store: GC arrays

Small-footprint rules for `array.new_fixed`, `array.get` and `array.set`
(`STriple.arrayNewFixed`, `STriple.arrayGet`, `STriple.arraySet`), with element
points-to assertions `pointsTo (.elem a i) (.fv fv)` and whole-array assertions
`arrayPts a fs`, holding in every run and every profile. `array.new_fixed`
allocates fresh cells (the frame's cells are at addresses below
`s.arrays.length`); `array.set` changes one cell and keeps every other
(`cellOf_setArrayField_ne`). The instruction rules used are those of
`Silmaril.Wasm.Logic.Instr.Thms` (`Hoare.Wp.arrayGet`, `Hoare.Wp.arraySet`,
`Hoare.Wp.arrayNewFixed`) at `Wp .part = HWP`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Sep

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Cells of the store -/

theorem cellOf_elem {s : Store H} {a i : Nat} {c : Cell} (h : cellOf s (.elem a i) = some c) :
    ∃ ai fv, s.arrays[a]? = some ai ∧ ai.fields[i]? = some fv ∧ c = .fv fv := by
  simp only [cellOf, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨fv, ⟨ai, hs, hf⟩, rfl⟩ := h
  exact ⟨ai, fv, hs, hf, rfl⟩

theorem cellOf_elem_lt {s : Store H} {a i : Nat} {c : Cell} (h : cellOf s (.elem a i) = some c) :
    a < s.arrays.length := by
  obtain ⟨ai, fv, hs, -, -⟩ := cellOf_elem h
  exact (List.getElem?_eq_some_iff.mp hs).1

theorem cellOf_addArray_old {s : Store H} {ai : ArrayInst} {l : Loc} {c : Cell}
    (h : cellOf s l = some c) : cellOf (s.addArray ai) l = some c := by
  cases l with
  | elem a i =>
    obtain ⟨ai', fv, hs, hf, rfl⟩ := cellOf_elem h
    have ha : a < s.arrays.length := (List.getElem?_eq_some_iff.mp hs).1
    simp [cellOf, Store.addArray, List.getElem?_append_left ha, hs, hf]
  | _ => exact h

theorem cellOf_addArray_new {s : Store H} {ai : ArrayInst} {i : Nat} :
    cellOf (s.addArray ai) (.elem s.arrays.length i) = ai.fields[i]?.map .fv := by
  simp [cellOf, Store.addArray]

theorem cellOf_setArrayField_same {s : Store H} {a i : Nat} {ai : ArrayInst} {fv : FieldVal}
    (hs : s.arrays[a]? = some ai) (hi : i < ai.fields.length) :
    cellOf (s.setArrayField a i fv) (.elem a i) = some (.fv fv) := by
  simp [cellOf, Store.setArrayField, hs, hi]

theorem cellOf_setArrayField_ne {s : Store H} {a i : Nat} {fv : FieldVal} {l : Loc}
    (hl : l ≠ .elem a i) : cellOf (s.setArrayField a i fv) l = cellOf s l := by
  cases l with
  | elem a' i' =>
    by_cases ha : a = a'
    · subst ha
      have hi : i ≠ i' := fun h => hl (h ▸ rfl)
      simp only [cellOf, Store.setArrayField, List.getElem?_modify]
      cases s.arrays[a]? <;> simp [List.getElem?_set_ne hi]
    · simp [cellOf, Store.setArrayField, ha]
  | _ => rfl

/-! ## Rules -/

/-- **`array.get`**: `{a[i] ↦ fv} array.get {a[i] ↦ fv ∧ result unpack(fv)}`. -/
theorem STriple.arrayGet {us : List Val} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32}
    {a : Nat} {fv : FieldVal} {d : DefType} {ft : CFieldType} (he : Expand d (.array ft))
    (hu : unpackable (fieldStorage ft) sx fv) :
    STriple P host (fun f h => f.type? x = some d ∧ pointsTo (.elem a i.toNat) (.fv fv) h)
      (vals (us ++ [.ref (.array a), .i32 i]) ++ [.plain (.arrayGet sx x)])
      (fun _ o h => o = .normal (us ++ [unpackField sx fv]) ∧
        pointsTo (.elem a i.toNat) (.fv fv) h) := by
  rintro s f _ hF hd hsat ⟨hty, rfl⟩
  have hc : cellOf s (.elem a i.toNat) = some (.fv fv) :=
    hsat _ _ (Heap.union_left (single_self _ _))
  obtain ⟨ai, fv', hs, hf, hfv⟩ := cellOf_elem hc
  obtain rfl : fv' = fv := by injection hfv with h; exact h.symm
  have hq : HWP P host s f (vals (us ++ [unpackField sx fv'])) fun s' f' o =>
      ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧
        o = .normal (us ++ [unpackField sx fv']) ∧ pointsTo (.elem a i.toNat) (.fv fv') hQ :=
    HWP.of_vals ⟨_, hd, hsat, rfl, rfl⟩
  exact Wp.arrayGet (m := .part) hs hf hty he hu (by simpa using hq)

/-- **`array.set`**: `{a[i] ↦ _} array.set {a[i] ↦ pack(v)}`. -/
theorem STriple.arraySet {us : List Val} {x : TypeIdx} {i : BitVec 32} {a : Nat} {v : Val}
    {fv : FieldVal} {d : DefType} {ft : CFieldType} (he : Expand d (.array ft))
    (hp : packable (fieldStorage ft) v) :
    STriple P host (fun f h => f.type? x = some d ∧ pointsTo (.elem a i.toNat) (.fv fv) h)
      (vals (us ++ [.ref (.array a), .i32 i, v]) ++ [.plain (.arraySet x)])
      (fun _ o h => o = .normal us ∧
        pointsTo (.elem a i.toNat) (.fv (packField (fieldStorage ft) v)) h) := by
  rintro s f _ hF hd hsat ⟨hty, rfl⟩
  have hc : cellOf s (.elem a i.toNat) = some (.fv fv) :=
    hsat _ _ (Heap.union_left (single_self _ _))
  obtain ⟨ai, fv', hs, hf, -⟩ := cellOf_elem hc
  have hlt : i.toNat < ai.fields.length := (List.getElem?_eq_some_iff.mp hf).1
  have hsat' := sat_set (c' := .fv (packField (fieldStorage ft) v)) hd hsat
    (cellOf_setArrayField_same hs hlt) fun _ hl => cellOf_setArrayField_ne hl
  have hq : HWP P host (s.setArrayField a i.toNat (packField (fieldStorage ft) v)) f (vals us)
      fun s' f' o => ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧ o = .normal us ∧
        pointsTo (.elem a i.toNat) (.fv (packField (fieldStorage ft) v)) hQ :=
    HWP.of_vals ⟨_, single_disj hd, hsat', rfl, rfl⟩
  exact Wp.arraySet (m := .part) hs hlt hty he hp (by simpa using hq)

/-- A fresh array is disjoint from every heap the store satisfies. -/
theorem array_disj {s : Store H} {fs : List FieldVal} {hF : Heap} (hsat : Heap.Sat s hF) :
    Heap.Disj (Heap.array s.arrays.length fs) hF := fun l => by
  cases hl : hF l with
  | none => exact .inr rfl
  | some c =>
    refine .inl ?_
    cases l with
    | elem a i =>
      have ha : a < s.arrays.length := cellOf_elem_lt (hsat _ _ hl)
      simp [Heap.array, Nat.ne_of_lt ha]
    | _ => rfl

/-- The store after an allocation satisfies the new array and the frame. -/
theorem sat_addArray {s : Store H} {ai : ArrayInst} {hF : Heap} (hsat : Heap.Sat s hF) :
    Heap.Sat (s.addArray ai) ((Heap.array s.arrays.length ai.fields).union hF) := by
  intro l c h
  rcases Heap.union_some h with h₁ | ⟨-, h₂⟩
  · cases l with
    | elem a i =>
      by_cases ha : a = s.arrays.length
      · subst ha
        simpa [Heap.array, cellOf_addArray_new] using h₁
      · simp [Heap.array, ha] at h₁
    | _ => simp [Heap.array] at h₁
  · exact cellOf_addArray_old (hsat _ _ h₂)

/-- **`array.new_fixed`**: `{emp} array.new_fixed {a ↦ elements}` for a fresh
address `a`. -/
theorem STriple.arrayNewFixed {us vs : List Val} {x : TypeIdx} {n : Fin (2 ^ 32)} {d : DefType}
    {ft : CFieldType} (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
    STriple P host (fun f h => f.type? x = some d ∧ emp h)
      (vals (us ++ vs) ++ [.plain (.arrayNewFixed x n)])
      (fun _ o h => ∃ a, o = .normal (us ++ [.ref (.array a)]) ∧
        arrayPts a (vs.map (packField (fieldStorage ft))) h) := by
  rintro s f _ hF hd hsat ⟨hty, rfl⟩
  have hsF : Heap.Sat s hF := Heap.Sat.right hd hsat
  have hq : HWP P host (s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩) f
      (vals (us ++ [.ref (.array s.arrays.length)])) fun s' f' o =>
        ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧
          ∃ a, o = .normal (us ++ [.ref (.array a)]) ∧
            arrayPts a (vs.map (packField (fieldStorage ft))) hQ :=
    HWP.of_vals ⟨_, array_disj hsF,
      sat_addArray (ai := ⟨d, vs.map (packField (fieldStorage ft))⟩) hsF, _, rfl, rfl⟩
  exact Wp.arrayNewFixed (m := .part) hty he hn hp (by simpa using hq)

end Silmaril.Wasm.Logic.Sep
