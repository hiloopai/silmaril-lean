module

public import Silmaril.Proofs.Wasm.Logic.Iris.Table

/-!
# The Iris logic of Wasm Core 3.0: GC structures and arrays

`wp_structNew`, `wp_structGet`, `wp_structGet_null`, `wp_structSet`,
`wp_arrayNew`, `wp_arrayNewFixed`, `wp_arrayGet`, `wp_arraySet`, `wp_arrayLen`. Allocation gives
the points-to cells of the new object at a fresh address; field and element
accesses need the cell of the field or element (which proves the access in
bounds), plus the frame for the type of the instruction.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head)
open Silmaril.Wasm.Logic.Hoare (newFields)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem type?_det {f : Frame} {x : TypeIdx} {d d' : DefType} (hd : f.type? x = some d)
    (hd' : f.type? x = some d') : d' = d :=
  Option.some.inj (hd'.symm.trans hd)

theorem expand_struct_det {d : DefType} {fs fs' : Ty (.list .field)} (he : Expand d (.struct fs))
    (he' : Expand d (.struct fs')) : fs' = fs := by
  have h₂ := SingleThreaded.Det.Expand.det he' he
  injection h₂

theorem expand_array_det {d : DefType} {ft ft' : CFieldType} (he : Expand d (.array ft))
    (he' : Expand d (.array ft')) : ft' = ft := by
  have h₂ := SingleThreaded.Det.Expand.det he' he
  injection h₂

/-! ## Structures -/

/-- The cells of a field access. -/
abbrev fieldCells (f : Frame) (a j : Nat) (fv : FieldVal) : List (ILoc × ICell) :=
  [(.frame, .frame f), (.field a j, .field fv)]

theorem field_of_cells {s : Store H} {f f' : Frame} {a j : Nat} {fv : FieldVal}
    (h : Cells (fieldCells f a j fv) s f') :
    ∃ si, s.structs[a]? = some si ∧ si.fields[j]? = some fv := by
  have h₁ : cellOf s f' (.field a j) = some (.field fv) := h (.field a j, .field fv) (by simp)
  rcases hs : s.structs[a]? with _ | si
  · simp [cellOf, hs] at h₁
  · exact ⟨si, rfl, by simpa [cellOf, hs] using h₁⟩

theorem structNew_change {s : Store H} {f : Frame} {si : StructInst} :
    Change s f (s.addStruct si) f [(.frame, .frame f)] [(.frame, .frame f)]
      (structCells s.structs.length si.fields) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · have hb := nodup_idxCells (cell := ICell.field) (fun _ _ h => by injection h) 0 si.fields
      (loc := ILoc.field s.structs.length)
    rw [fst_idxCells] at hb ⊢
    simpa using hb
  · intro q hq
    obtain ⟨k, -, rfl⟩ := mem_idxCells.mp hq
    exact cellOf_field_fresh _
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [List.mem_singleton] at hp
      rw [hp]
      rfl
    · obtain ⟨k, hk, rfl⟩ := mem_idxCells.mp hp
      exact cellOf_addStruct_new (by simp)
  · intro l c _ hc
    exact cellOf_addStruct_old hc

theorem structNew_inv {us vs : List Val} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    {f : Frame} {rest : List Admin} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hn : vs.length = fs.length) (s : Store H) (f' : Frame) (us' args : List Val)
    (c₀ : Config H) (hc : Cells [(.frame, .frame f)] s f') (hW : us ++ vs = us' ++ args)
    (hh : Head P s f' args (.plain (.structNew x)) c₀) :
    vals us' ++ c₀.code ++ rest = vals (us ++ [.ref (.struct s.structs.length)]) ++ rest ∧
      Change s f' c₀.store c₀.frame [(.frame, .frame f)] [(.frame, .frame f)]
        (structCells s.structs.length (newFields fs vs)) := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨d', fs', hd', he', hn', rfl⟩ := Hoare.head_structNew hh
  obtain rfl : d' = d := type?_det hd (hf ▸ hd')
  obtain rfl : fs' = fs := expand_struct_det he he'
  obtain ⟨rfl, rfl⟩ := Hoare.split_args hW (hn'.trans hn.symm)
  subst hf
  exact ⟨by simp [vals, Val.toAdmin], structNew_change⟩

theorem structGet_inv {us : List Val} {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx}
    {a : Nat} {fv : FieldVal} {f : Frame} {rest : List Admin} (s : Store H) (f' : Frame)
    (us' args : List Val) (c₀ : Config H) (hc : Cells (fieldCells f a i.toNat fv) s f')
    (hW : us ++ [.ref (.struct a)] = us' ++ args)
    (hh : Head P s f' args (.plain (.structGet sx x i)) c₀) :
    c₀.store = s ∧ c₀.frame = f' ∧
      vals us' ++ c₀.code ++ rest = vals (us ++ [unpackField sx fv]) ++ rest := by
  obtain ⟨si, hsi, hfv⟩ := field_of_cells hc
  rcases Hoare.head_structGet hh with ⟨rfl, -⟩ | ⟨a', si', fv', rfl, hs', hf', rfl⟩
  · obtain ⟨-, hv⟩ := Hoare.split_one hW
    exact absurd hv (by simp)
  · obtain ⟨rfl, hv⟩ := Hoare.split_one hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : si' = si := Option.some.inj (hs'.symm.trans hsi)
    obtain rfl : fv' = fv := Option.some.inj (hf'.symm.trans hfv)
    simp [vals]

theorem structSet_change {s : Store H} {f : Frame} {a j : Nat} {si : StructInst}
    {fv₀ fv : FieldVal} (hsi : s.structs[a]? = some si) (hj : j < si.fields.length) :
    Change s f (s.setStructField a j fv) f (fieldCells f a j fv₀) (fieldCells f a j fv) [] := by
  refine ⟨rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rfl
    · exact cellOf_setStructField_self hsi hj
  · intro l c hl hlc
    have hne : l ≠ .field a j := fun he => hl (by simp [he])
    rw [cellOf_setStructField_ne hne]
    exact hlc

theorem structSet_inv {us : List Val} {x : TypeIdx} {i : FieldIdx} {a : Nat} {v : Val}
    {fv₀ : FieldVal} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType} {f : Frame}
    {rest : List Admin} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some ft) (s : Store H) (f' : Frame) (us' args : List Val)
    (c₀ : Config H) (hc : Cells (fieldCells f a i.toNat fv₀) s f')
    (hW : us ++ [.ref (.struct a), v] = us' ++ args)
    (hh : Head P s f' args (.plain (.structSet x i)) c₀) :
    vals us' ++ c₀.code ++ rest = vals us ++ rest ∧
      Change s f' c₀.store c₀.frame (fieldCells f a i.toNat fv₀)
        (fieldCells f a i.toNat (packField (fieldStorage ft) v)) [] := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨si, hsi, hfv⟩ := field_of_cells hc
  rcases Hoare.head_structSet hh with ⟨v', rfl, -⟩ | ⟨a', v', d', fs', ft', rfl, hd', he', hi', rfl⟩
  · obtain ⟨-, hv, -⟩ := Hoare.split_two hW
    exact absurd hv (by simp)
  · obtain ⟨rfl, hv, rfl⟩ := Hoare.split_two hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : d' = d := type?_det hd (hf ▸ hd')
    obtain rfl : fs' = fs := expand_struct_det he he'
    obtain rfl : ft' = ft := Option.some.inj (hi'.symm.trans hi)
    exact ⟨by simp, hf ▸ structSet_change hsi (List.getElem?_eq_some_iff.mp hfv).1⟩

/-! ## Arrays -/

/-- The cells of an element access. -/
abbrev elemCells (f : Frame) (a j : Nat) (fv : FieldVal) : List (ILoc × ICell) :=
  [(.frame, .frame f), (.elem a j, .field fv)]

theorem elem_of_cells {s : Store H} {f f' : Frame} {a j : Nat} {fv : FieldVal}
    (h : Cells (elemCells f a j fv) s f') :
    ∃ ai, s.arrays[a]? = some ai ∧ ai.fields[j]? = some fv := by
  have h₁ : cellOf s f' (.elem a j) = some (.field fv) := h (.elem a j, .field fv) (by simp)
  rcases hs : s.arrays[a]? with _ | ai
  · simp [cellOf, hs] at h₁
  · exact ⟨ai, rfl, by simpa [cellOf, hs] using h₁⟩

theorem arrayNew_nodup (f : Frame) (b : Nat) (fvs : List FieldVal) :
    (([(.frame, .frame f)] : List (ILoc × ICell)).map Prod.fst ++
      (arrayCells b fvs).map Prod.fst).Nodup := by
  have hb : ((idxCells (.elem b) .field 0 fvs).map Prod.fst).Nodup :=
    nodup_idxCells (fun _ _ h => by injection h) 0 fvs
  rw [fst_idxCells] at hb
  simp only [arrayCells, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    fst_idxCells]
  simpa using hb

theorem arrayNew_fresh {s : Store H} {f : Frame} (fvs : List FieldVal) :
    ∀ q ∈ arrayCells s.arrays.length fvs, cellOf s f q.1 = none := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact cellOf_array_fresh (.inl rfl)
  · obtain ⟨k, -, rfl⟩ := mem_idxCells.mp hq
    exact cellOf_array_fresh (.inr ⟨_, rfl⟩)

theorem arrayNew_new {s : Store H} {f : Frame} {ai : ArrayInst} :
    Cells ([(.frame, .frame f)] ++ arrayCells s.arrays.length ai.fields) (s.addArray ai) f := by
  intro p hp
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · rfl
  · exact cellOf_addArray_len
  · obtain ⟨k, hk, rfl⟩ := mem_idxCells.mp hp
    exact cellOf_addArray_elem (by simp)

theorem arrayNew_change {s : Store H} {f : Frame} {ai : ArrayInst} :
    Change s f (s.addArray ai) f [(.frame, .frame f)] [(.frame, .frame f)]
      (arrayCells s.arrays.length ai.fields) :=
  ⟨rfl, arrayNew_nodup f _ _, arrayNew_fresh _, arrayNew_new,
    fun _ _ _ hc => cellOf_addArray_old hc⟩

theorem arrayNewFixed_inv {us vs : List Val} {x : TypeIdx} {n : Fin (2 ^ 32)} {d : DefType}
    {ft : CFieldType} {f : Frame} {rest : List Admin} (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hn : vs.length = n.val) (s : Store H) (f' : Frame)
    (us' args : List Val) (c₀ : Config H) (hc : Cells [(.frame, .frame f)] s f')
    (hW : us ++ vs = us' ++ args) (hh : Head P s f' args (.plain (.arrayNewFixed x n)) c₀) :
    vals us' ++ c₀.code ++ rest = vals (us ++ [.ref (.array s.arrays.length)]) ++ rest ∧
      Change s f' c₀.store c₀.frame [(.frame, .frame f)] [(.frame, .frame f)]
        (arrayCells s.arrays.length (vs.map (packField (fieldStorage ft)))) := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨d', ft', hd', he', hn', rfl⟩ := head_arrayNewFixed hh
  obtain rfl : d' = d := type?_det hd (hf ▸ hd')
  obtain rfl : ft' = ft := expand_array_det he he'
  obtain ⟨rfl, rfl⟩ := Hoare.split_args hW (hn'.trans hn.symm)
  subst hf
  exact ⟨by simp [vals, Val.toAdmin, arrRef], arrayNew_change⟩

theorem arrayGet_inv {us : List Val} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32}
    {a : Nat} {fv : FieldVal} {f : Frame} {rest : List Admin} (s : Store H) (f' : Frame)
    (us' args : List Val) (c₀ : Config H) (hc : Cells (elemCells f a i.toNat fv) s f')
    (hW : us ++ [.ref (.array a), .i32 i] = us' ++ args)
    (hh : Head P s f' args (.plain (.arrayGet sx x)) c₀) :
    c₀.store = s ∧ c₀.frame = f' ∧
      vals us' ++ c₀.code ++ rest = vals (us ++ [unpackField sx fv]) ++ rest := by
  obtain ⟨ai, hai, hfv⟩ := elem_of_cells hc
  rcases head_arrayGet hh with ⟨i', rfl, -⟩ | ⟨a', i', ai', rfl, ha', hlt, -⟩ |
      ⟨a', i', ai', fv', rfl, ha', hf', rfl⟩
  · obtain ⟨-, hv, -⟩ := Hoare.split_two hW
    exact absurd hv (by simp)
  · obtain ⟨-, hv, hi⟩ := Hoare.split_two hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : i' = i := Hoare.numVal_int_inj (by simpa [Val.i32] using hi)
    obtain rfl : ai' = ai := Option.some.inj (ha'.symm.trans hai)
    exact absurd (List.getElem?_eq_some_iff.mp hfv).1 (by omega)
  · obtain ⟨rfl, hv, hi⟩ := Hoare.split_two hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : i' = i := Hoare.numVal_int_inj (by simpa [Val.i32] using hi)
    obtain rfl : ai' = ai := Option.some.inj (ha'.symm.trans hai)
    obtain rfl : fv' = fv := Option.some.inj (hf'.symm.trans hfv)
    simp [vals]

theorem arraySet_change {s : Store H} {f : Frame} {a j : Nat} {ai : ArrayInst}
    {fv₀ fv : FieldVal} (hai : s.arrays[a]? = some ai) (hj : j < ai.fields.length) :
    Change s f (s.setArrayField a j fv) f (elemCells f a j fv₀) (elemCells f a j fv) [] := by
  refine ⟨rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rfl
    · exact cellOf_setArrayField_self hai hj
  · intro l c hl hlc
    have hne : l ≠ .elem a j := fun he => hl (by simp [he])
    rw [cellOf_setArrayField_ne hne]
    exact hlc

theorem split_three {us us' : List Val} {v₁ v₂ v₃ w₁ w₂ w₃ : Val}
    (hW : us ++ [v₁, v₂, v₃] = us' ++ [w₁, w₂, w₃]) :
    us' = us ∧ w₁ = v₁ ∧ w₂ = v₂ ∧ w₃ = v₃ := by
  have h₂ := List.append_inj' hW rfl
  simp only [List.cons.injEq, and_true] at h₂
  exact ⟨h₂.1.symm, h₂.2.1.symm, h₂.2.2.1.symm, h₂.2.2.2.symm⟩

theorem arraySet_inv {us : List Val} {x : TypeIdx} {i : BitVec 32} {a : Nat} {v : Val}
    {fv₀ : FieldVal} {d : DefType} {ft : CFieldType} {f : Frame} {rest : List Admin}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (s : Store H) (f' : Frame)
    (us' args : List Val) (c₀ : Config H) (hc : Cells (elemCells f a i.toNat fv₀) s f')
    (hW : us ++ [.ref (.array a), .i32 i, v] = us' ++ args)
    (hh : Head P s f' args (.plain (.arraySet x)) c₀) :
    vals us' ++ c₀.code ++ rest = vals us ++ rest ∧
      Change s f' c₀.store c₀.frame (elemCells f a i.toNat fv₀)
        (elemCells f a i.toNat (packField (fieldStorage ft) v)) [] := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨ai, hai, hfv⟩ := elem_of_cells hc
  have hj : i.toNat < ai.fields.length := (List.getElem?_eq_some_iff.mp hfv).1
  rcases head_arraySet hh with ⟨i', v', rfl, -⟩ | ⟨a', i', v', ai', rfl, ha', hlt, -⟩ |
      ⟨a', i', v', d', ft', rfl, hd', he', rfl⟩
  · exact absurd (split_three hW).2.1 (by simp)
  · obtain ⟨-, hv, hi, -⟩ := split_three hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : i' = i := Hoare.numVal_int_inj (by simpa [Val.i32] using hi)
    obtain rfl : ai' = ai := Option.some.inj (ha'.symm.trans hai)
    omega
  · obtain ⟨rfl, hv, hi, rfl⟩ := split_three hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : i' = i := Hoare.numVal_int_inj (by simpa [Val.i32] using hi)
    obtain rfl : d' = d := type?_det hd (hf ▸ hd')
    obtain rfl : ft' = ft := expand_array_det he he'
    exact ⟨by simp, hf ▸ arraySet_change hai hj⟩

theorem arrayLen_inv {us : List Val} {a n : Nat} {rest : List Admin} (s : Store H) (f : Frame)
    (us' args : List Val) (c₀ : Config H) (hc : Cells [(.arrLen a, .len n)] s f)
    (hW : us ++ [.ref (.array a)] = us' ++ args) (hh : Head P s f args (.plain .arrayLen) c₀) :
    c₀.store = s ∧ c₀.frame = f ∧
      vals us' ++ c₀.code ++ rest = vals (us ++ [.i32 (BitVec.ofNat 32 n)]) ++ rest := by
  have h₁ : cellOf s f (.arrLen a) = some (.len n) := hc (.arrLen a, .len n) (by simp)
  rcases head_arrayLen hh with ⟨rfl, -⟩ | ⟨a', ai, rfl, ha, rfl⟩
  · exact absurd (Hoare.split_one hW).2 (by simp)
  · obtain ⟨rfl, hv⟩ := Hoare.split_one hW
    obtain rfl : a' = a := by simpa using hv
    have hn : ai.fields.length = n := by simpa [cellOf, ha] using h₁
    subst hn
    simp [vals, constI32]

section Rules

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- **`struct.new`**: the new structure is allocated at a fresh address `a` with the
(packed) fields. -/
theorem wp_structNew {E : CoPset} {us vs : List Val} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
    ownFrame f ∗ ▷ (∀ a, ownFrame f -∗ ownStruct a (newFields fs vs) -∗
      WP (IExpr.run (vals (us ++ [.ref (.struct a)]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ vs) ++ .plain (.structNew x) :: rest) : IExpr P host) @ E
      {{ Φ }} := by
  iintro ⟨Hf, H⟩
  iapply wp_head_change [(.frame, .frame f)] [(.frame, .frame f)]
    (fun s => structCells s.structs.length (newFields fs vs))
    (fun s => vals (us ++ [.ref (.struct s.structs.length)]) ++ rest) ⟨rfl, by simp, rfl⟩
    (fun s f' hc => ⟨us, vs, _, rfl, .aggregate (.structNew ((frame_of_cells hc) ▸ hd) he hn hp)⟩)
    (structNew_inv hd he hn)
  simp only [ownCells_one]
  iframe Hf
  iintro !> %s Hf Hs
  iapply H $$ %s.structs.length Hf Hs

/-- **`struct.get`** on a structure: reads the (unpacked) field. -/
theorem wp_structGet {E : CoPset} {us : List Val} {sx : Option Signedness} {x : TypeIdx}
    {i : FieldIdx} {a : Nat} {fv : FieldVal} {d : DefType} {fs : Ty (.list .field)}
    {ft : CFieldType} {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu : unpackable (fieldStorage ft) sx fv) :
    ownFrame f ∗ pts (.field a i.toNat) (.field fv) ∗
      ▷ (ownFrame f ∗ pts (.field a i.toNat) (.field fv) -∗
        WP (IExpr.run (vals (us ++ [unpackField sx fv]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ [.ref (.struct a)]) ++ .plain (.structGet sx x i) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  simpa only [fieldCells, ownCells_two, sep_assoc.to_eq] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ) (fieldCells f a i.toNat fv)
      ⟨rfl, by simp, rfl⟩
      (fun s f' hc => by
        obtain ⟨si, hsi, hfv⟩ := field_of_cells hc
        exact ⟨us, _, _, rfl,
          .aggregate (.structGetStruct hsi hfv ((frame_of_cells hc) ▸ hd) he hi hu)⟩)
      structGet_inv

/-- **`struct.get`** on a null reference traps. -/
theorem wp_structGet_null {E : CoPset} {us : List Val} {sx : Option Signedness} {x : TypeIdx}
    {i : FieldIdx} {rest : List Admin} {Φ : Res H → IProp GF} :
    ▷ (emp -∗ WP (IExpr.run (vals us ++ .trap :: rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ [.ref .null]) ++ .plain (.structGet sx x i) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_head_read (P := P) (host := host) (E := E) (Φ := Φ)
    (code' := vals us ++ .trap :: rest) [] ⟨rfl, by simp, rfl⟩
    (fun _ _ _ => ⟨us, _, _, rfl, .aggregate .structGetNull⟩)
    (fun s f us' args c₀ _ hW hh => by
      rcases Hoare.head_structGet hh with ⟨rfl, rfl⟩ | ⟨a', si', fv', rfl, -, -, -⟩
      · obtain ⟨rfl, -⟩ := Hoare.split_one hW
        exact ⟨rfl, rfl, by simp⟩
      · exact absurd (Hoare.split_one hW).2 (by simp))
  simp only [ownCells_nil]
  isplitr
  · iempintro
  · iexact H

/-- **`struct.set`** on a structure: writes the (packed) field. -/
theorem wp_structSet {E : CoPset} {us : List Val} {x : TypeIdx} {i : FieldIdx} {a : Nat}
    {v : Val} {fv₀ : FieldVal} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType}
    {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hp : packable (fieldStorage ft) v) :
    ownFrame f ∗ pts (.field a i.toNat) (.field fv₀) ∗
      ▷ (ownFrame f ∗ pts (.field a i.toNat) (.field (packField (fieldStorage ft) v)) -∗
        WP (IExpr.run (vals us ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ [.ref (.struct a), v]) ++ .plain (.structSet x i) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hf, Hc, H⟩
  iapply wp_head_change (fieldCells f a i.toNat fv₀)
    (fieldCells f a i.toNat (packField (fieldStorage ft) v)) (fun _ => []) (fun _ => vals us ++ rest)
    ⟨rfl, by simp, rfl⟩
    (fun s f' hc => by
      obtain ⟨si, hsi, hfv⟩ := field_of_cells hc
      exact ⟨us, _, _, rfl, .aggregate (.structSetStruct ((frame_of_cells hc) ▸ hd) he hi hsi
        (List.getElem?_eq_some_iff.mp hfv).1 hp)⟩)
    (structSet_inv hd he hi)
  simp only [fieldCells, ownCells_two, ownCells_nil]
  iframe Hf Hc
  iintro !> %_ Hc -
  iapply H $$ Hc

/-- **`array.new_fixed`**: the new array is allocated at a fresh address `a` with the
(packed) elements and its length. (`array.new` reduces to `array.new_fixed` in one
step.) -/
theorem wp_arrayNewFixed {E : CoPset} {us vs : List Val} {x : TypeIdx} {n : Fin (2 ^ 32)}
    {d : DefType} {ft : CFieldType} {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
    ownFrame f ∗ ▷ (∀ a, ownFrame f -∗ ownArray a (vs.map (packField (fieldStorage ft))) -∗
      WP (IExpr.run (vals (us ++ [.ref (.array a)]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ vs) ++ .plain (.arrayNewFixed x n) :: rest) : IExpr P host) @ E
      {{ Φ }} := by
  iintro ⟨Hf, H⟩
  iapply wp_head_change [(.frame, .frame f)] [(.frame, .frame f)]
    (fun s => arrayCells s.arrays.length (vs.map (packField (fieldStorage ft))))
    (fun s => vals (us ++ [.ref (.array s.arrays.length)]) ++ rest) ⟨rfl, by simp, rfl⟩
    (fun s f' hc =>
      ⟨us, vs, _, rfl, .aggregate (.arrayNewFixed ((frame_of_cells hc) ▸ hd) he hn hp)⟩)
    (arrayNewFixed_inv hd he hn)
  simp only [ownCells_one]
  iframe Hf
  iintro !> %s Hf Ha
  iapply H $$ %s.arrays.length Hf Ha

/-- **`array.new`**: `n` copies of `v`, then `array.new_fixed`. -/
theorem wp_arrayNew {E : CoPset} {us : List Val} {v : Val} {n : BitVec 32} {x : TypeIdx}
    {rest : List Admin} {Φ : Res H → IProp GF} :
    ▷ WP (IExpr.run (vals (us ++ List.replicate n.toNat v) ++
        .plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩) :: rest) : IExpr P host) @ E {{ Φ }}
    ⊢ WP (IExpr.run (vals (us ++ [v, .i32 n]) ++ .plain (.arrayNew x) :: rest) : IExpr P host) @ E
      {{ Φ }} := by
  iintro H
  iapply wp_head_read (P := P) (host := host) (E := E) (Φ := Φ)
    (code' := vals (us ++ List.replicate n.toNat v) ++
      .plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩) :: rest) [] ⟨rfl, by simp, rfl⟩
    (fun _ _ _ => ⟨us, _, _, rfl, .aggregate (.arrayNew v n)⟩)
    (fun s f us' args c₀ _ hW hh => by
      obtain ⟨v', n', rfl, rfl⟩ := head_arrayNew hh
      obtain ⟨rfl, hv, hn⟩ := Hoare.split_two hW
      obtain rfl := hv
      obtain rfl : n' = n := Hoare.numVal_int_inj (by simpa [Val.i32] using hn)
      exact ⟨rfl, rfl, by simp [vals]⟩)
  simp only [ownCells_nil]
  isplitr
  · iempintro
  · iintro !> -
    iexact H

/-- **`array.get`** on an array: reads the (unpacked) element. -/
theorem wp_arrayGet {E : CoPset} {us : List Val} {sx : Option Signedness} {x : TypeIdx}
    {i : BitVec 32} {a : Nat} {fv : FieldVal} {d : DefType} {ft : CFieldType}
    {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hu : unpackable (fieldStorage ft) sx fv) :
    ownFrame f ∗ pts (.elem a i.toNat) (.field fv) ∗
      ▷ (ownFrame f ∗ pts (.elem a i.toNat) (.field fv) -∗
        WP (IExpr.run (vals (us ++ [unpackField sx fv]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ [.ref (.array a), .i32 i]) ++ .plain (.arrayGet sx x) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  simpa only [elemCells, ownCells_two, sep_assoc.to_eq] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ) (elemCells f a i.toNat fv)
      ⟨rfl, by simp, rfl⟩
      (fun s f' hc => by
        obtain ⟨ai, hai, hfv⟩ := elem_of_cells hc
        exact ⟨us, _, _, rfl,
          .aggregate (.arrayGetArray hai hfv ((frame_of_cells hc) ▸ hd) he hu)⟩)
      arrayGet_inv

/-- **`array.set`** on an array: writes the (packed) element. -/
theorem wp_arraySet {E : CoPset} {us : List Val} {x : TypeIdx} {i : BitVec 32} {a : Nat}
    {v : Val} {fv₀ : FieldVal} {d : DefType} {ft : CFieldType} {rest : List Admin} {f : Frame}
    {Φ : Res H → IProp GF} (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hp : packable (fieldStorage ft) v) :
    ownFrame f ∗ pts (.elem a i.toNat) (.field fv₀) ∗
      ▷ (ownFrame f ∗ pts (.elem a i.toNat) (.field (packField (fieldStorage ft) v)) -∗
        WP (IExpr.run (vals us ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ [.ref (.array a), .i32 i, v]) ++ .plain (.arraySet x) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hf, Hc, H⟩
  iapply wp_head_change (elemCells f a i.toNat fv₀)
    (elemCells f a i.toNat (packField (fieldStorage ft) v)) (fun _ => []) (fun _ => vals us ++ rest)
    ⟨rfl, by simp, rfl⟩
    (fun s f' hc => by
      obtain ⟨ai, hai, hfv⟩ := elem_of_cells hc
      exact ⟨us, _, _, rfl, .aggregate (.arraySetArray hai (List.getElem?_eq_some_iff.mp hfv).1
        ((frame_of_cells hc) ▸ hd) he hp)⟩)
    (arraySet_inv hd he)
  simp only [elemCells, ownCells_two, ownCells_nil]
  iframe Hf Hc
  iintro !> %_ Hc -
  iapply H $$ Hc

/-- **`array.len`**: reads the length cell (no frame needed). -/
theorem wp_arrayLen {E : CoPset} {us : List Val} {a n : Nat} {rest : List Admin}
    {Φ : Res H → IProp GF} :
    pts (.arrLen a) (.len n) ∗ ▷ (pts (.arrLen a) (.len n) -∗
      WP (IExpr.run (vals (us ++ [.i32 (BitVec.ofNat 32 n)]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ [.ref (.array a)]) ++ .plain .arrayLen :: rest) : IExpr P host)
      @ E {{ Φ }} := by
  simpa only [ownCells_one] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ) [(.arrLen a, .len n)]
      ⟨rfl, by simp, rfl⟩
      (fun s f hc => by
        have h₁ : cellOf s f (.arrLen a) = some (.len n) := hc (.arrLen a, .len n) (by simp)
        obtain ⟨ai, hai, -⟩ : ∃ ai, s.arrays[a]? = some ai ∧ ai.fields.length = n := by
          rcases ha : s.arrays[a]? with _ | ai <;> simp_all [cellOf]
        exact ⟨us, _, _, rfl, .aggregate (.arrayLenArray hai)⟩)
      arrayLen_inv

end Rules

end Silmaril.Wasm.Logic.IrisWasm
