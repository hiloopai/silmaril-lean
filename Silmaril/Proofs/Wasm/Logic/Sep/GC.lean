module

public import Silmaril.Proofs.Wasm.Logic.Sep.Basic

/-!
# Separation logic over the Core 3.0 store: GC structures

Small-footprint rules for `struct.new`, `struct.get` and `struct.set`
(`STriple.structNew`, `STriple.structGet`, `STriple.structSet`), each holding in
every run and every profile. `struct.new` allocates fresh cells (the frame's
cells are at addresses below `s.structs.length`); `struct.set` changes one cell
and keeps every other (`cellOf_setStructField_ne`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Sep

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP newFields)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Cells of the store -/

theorem cellOf_field {s : Store H} {a i : Nat} {c : Cell} (h : cellOf s (.field a i) = some c) :
    ∃ si fv, s.structs[a]? = some si ∧ si.fields[i]? = some fv ∧ c = .fv fv := by
  simp only [cellOf, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨fv, ⟨si, hs, hf⟩, rfl⟩ := h
  exact ⟨si, fv, hs, hf, rfl⟩

theorem cellOf_addStruct_old {s : Store H} {si : StructInst} {l : Loc} {c : Cell}
    (h : cellOf s l = some c) : cellOf (s.addStruct si) l = some c := by
  cases l with
  | field a i =>
    obtain ⟨si', fv, hs, hf, rfl⟩ := cellOf_field h
    have ha : a < s.structs.length := (List.getElem?_eq_some_iff.mp hs).1
    simp [cellOf, Store.addStruct, List.getElem?_append_left ha, hs, hf]
  | _ => exact h

theorem cellOf_addStruct_new {s : Store H} {si : StructInst} {i : Nat} :
    cellOf (s.addStruct si) (.field s.structs.length i) = si.fields[i]?.map .fv := by
  simp [cellOf, Store.addStruct]

theorem cellOf_field_lt {s : Store H} {a i : Nat} {c : Cell} (h : cellOf s (.field a i) = some c) :
    a < s.structs.length := by
  obtain ⟨si, fv, hs, -, -⟩ := cellOf_field h
  exact (List.getElem?_eq_some_iff.mp hs).1

theorem cellOf_setStructField_same {s : Store H} {a i : Nat} {si : StructInst} {fv : FieldVal}
    (hs : s.structs[a]? = some si) (hi : i < si.fields.length) :
    cellOf (s.setStructField a i fv) (.field a i) = some (.fv fv) := by
  simp [cellOf, Store.setStructField, hs, hi]

theorem cellOf_setStructField_ne {s : Store H} {a i : Nat} {fv : FieldVal} {l : Loc}
    (hl : l ≠ .field a i) : cellOf (s.setStructField a i fv) l = cellOf s l := by
  cases l with
  | field a' i' =>
    by_cases ha : a = a'
    · subst ha
      have hi : i ≠ i' := fun h => hl (h ▸ rfl)
      simp only [cellOf, Store.setStructField, List.getElem?_modify]
      cases s.structs[a]? <;> simp [List.getElem?_set_ne hi]
    · simp [cellOf, Store.setStructField, ha]
  | _ => rfl

theorem single_self (l : Loc) (c : Cell) : Heap.single l c l = some c := by simp [Heap.single]

theorem single_disj {l : Loc} {c c' : Cell} {h : Heap} (hd : Heap.Disj (Heap.single l c) h) :
    Heap.Disj (Heap.single l c') h := fun l' => by
  by_cases hl : l' = l
  · subst hl
    rcases hd l' with h₁ | h₁
    · simp [Heap.single] at h₁
    · exact .inr h₁
  · exact .inl (by simp [Heap.single, hl])

/-! ## Rules -/

/-- **`struct.get`**: `{a.i ↦ fv} struct.get {a.i ↦ fv ∧ result unpack(fv)}`. -/
theorem STriple.structGet {us : List Val} {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx}
    {a : Nat} {fv : FieldVal} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType}
    (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu : unpackable (fieldStorage ft) sx fv) :
    STriple P host (fun f h => f.type? x = some d ∧ pointsTo (.field a i.toNat) (.fv fv) h)
      (vals (us ++ [.ref (.struct a)]) ++ [.plain (.structGet sx x i)])
      (fun _ o h => o = .normal (us ++ [unpackField sx fv]) ∧ pointsTo (.field a i.toNat) (.fv fv) h) := by
  rintro s f _ hF hd hsat ⟨hty, rfl⟩
  have hc : cellOf s (.field a i.toNat) = some (.fv fv) := hsat _ _ (Heap.union_left (single_self _ _))
  obtain ⟨si, fv', hs, hf, hfv⟩ := cellOf_field hc
  obtain rfl : fv' = fv := by injection hfv with h; exact h.symm
  have hq : HWP P host s f (vals (us ++ [unpackField sx fv'])) fun s' f' o =>
      ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧
        o = .normal (us ++ [unpackField sx fv']) ∧ pointsTo (.field a i.toNat) (.fv fv') hQ :=
    HWP.of_vals ⟨_, hd, hsat, rfl, rfl⟩
  exact Silmaril.Wasm.Logic.Hoare.HWP.structGet hs hf hty he hi hu (by simpa using hq)

/-- The frame is kept when one cell changes. -/
theorem sat_set {s s' : Store H} {l : Loc} {c c' : Cell} {hF : Heap}
    (hd : Heap.Disj (Heap.single l c) hF) (hsat : Heap.Sat s ((Heap.single l c).union hF))
    (hnew : cellOf s' l = some c') (hold : ∀ l', l' ≠ l → cellOf s' l' = cellOf s l') :
    Heap.Sat s' ((Heap.single l c').union hF) := by
  intro l' c₀ h
  rcases Heap.union_some h with h₁ | ⟨h₁, h₂⟩
  · by_cases hl : l' = l
    · subst hl
      rw [single_self] at h₁
      cases h₁
      exact hnew
    · simp [Heap.single, hl] at h₁
  · have hl : l' ≠ l := by
      rintro rfl
      rcases hd l' with h₃ | h₃
      · simp [Heap.single] at h₃
      · rw [h₃] at h₂; cases h₂
    rw [hold l' hl]
    exact hsat l' c₀ (Heap.union_right (by simp [Heap.single, hl]) h₂)

/-- **`struct.set`**: `{a.i ↦ _} struct.set {a.i ↦ pack(v)}`. -/
theorem STriple.structSet {us : List Val} {x : TypeIdx} {i : FieldIdx} {a : Nat} {v : Val}
    {fv : FieldVal} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType}
    (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hp : packable (fieldStorage ft) v) :
    STriple P host (fun f h => f.type? x = some d ∧ pointsTo (.field a i.toNat) (.fv fv) h)
      (vals (us ++ [.ref (.struct a), v]) ++ [.plain (.structSet x i)])
      (fun _ o h => o = .normal us ∧
        pointsTo (.field a i.toNat) (.fv (packField (fieldStorage ft) v)) h) := by
  rintro s f _ hF hd hsat ⟨hty, rfl⟩
  have hc : cellOf s (.field a i.toNat) = some (.fv fv) := hsat _ _ (Heap.union_left (single_self _ _))
  obtain ⟨si, fv', hs, hf, -⟩ := cellOf_field hc
  have hlt : i.toNat < si.fields.length := (List.getElem?_eq_some_iff.mp hf).1
  have hsat' := sat_set (c' := .fv (packField (fieldStorage ft) v)) hd hsat
    (cellOf_setStructField_same hs hlt) fun _ hl => cellOf_setStructField_ne hl
  have hq : HWP P host (s.setStructField a i.toNat (packField (fieldStorage ft) v)) f (vals us)
      fun s' f' o => ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧ o = .normal us ∧
        pointsTo (.field a i.toNat) (.fv (packField (fieldStorage ft) v)) hQ :=
    HWP.of_vals ⟨_, single_disj hd, hsat', rfl, rfl⟩
  exact Silmaril.Wasm.Logic.Hoare.HWP.structSet hty he hi hs hlt hp (by simpa using hq)

/-- A fresh structure is disjoint from every heap the store satisfies. -/
theorem struct_disj {s : Store H} {fs : List FieldVal} {hF : Heap} (hsat : Heap.Sat s hF) :
    Heap.Disj (Heap.struct s.structs.length fs) hF := fun l => by
  cases hl : hF l with
  | none => exact .inr rfl
  | some c =>
    refine .inl ?_
    cases l with
    | field a i =>
      have ha : a < s.structs.length := cellOf_field_lt (hsat _ _ hl)
      simp [Heap.struct, Nat.ne_of_lt ha]
    | _ => rfl

/-- The store after an allocation satisfies the new structure and the frame. -/
theorem sat_addStruct {s : Store H} {si : StructInst} {hF : Heap} (hsat : Heap.Sat s hF) :
    Heap.Sat (s.addStruct si) ((Heap.struct s.structs.length si.fields).union hF) := by
  intro l c h
  rcases Heap.union_some h with h₁ | ⟨-, h₂⟩
  · cases l with
    | field a i =>
      by_cases ha : a = s.structs.length
      · subst ha
        simpa [Heap.struct, cellOf_addStruct_new] using h₁
      · simp [Heap.struct, ha] at h₁
    | _ => simp [Heap.struct] at h₁
  · exact cellOf_addStruct_old (hsat _ _ h₂)

/-- **`struct.new`**: `{emp} struct.new {a ↦ fields}` for a fresh address `a`. -/
theorem STriple.structNew {us vs : List Val} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
    STriple P host (fun f h => f.type? x = some d ∧ emp h)
      (vals (us ++ vs) ++ [.plain (.structNew x)])
      (fun _ o h => ∃ a, o = .normal (us ++ [.ref (.struct a)]) ∧ structPts a (newFields fs vs) h) := by
  rintro s f _ hF hd hsat ⟨hty, rfl⟩
  have hsF : Heap.Sat s hF := Heap.Sat.right hd hsat
  have hq : HWP P host (s.addStruct ⟨d, newFields fs vs⟩) f
      (vals (us ++ [.ref (.struct s.structs.length)])) fun s' f' o =>
        ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧
          ∃ a, o = .normal (us ++ [.ref (.struct a)]) ∧ structPts a (newFields fs vs) hQ :=
    HWP.of_vals ⟨_, struct_disj hsF, sat_addStruct (si := ⟨d, newFields fs vs⟩) hsF, _, rfl, rfl⟩
  exact Silmaril.Wasm.Logic.Hoare.HWP.structNew hty he hn hp (by simpa using hq)

end Silmaril.Wasm.Logic.Sep
