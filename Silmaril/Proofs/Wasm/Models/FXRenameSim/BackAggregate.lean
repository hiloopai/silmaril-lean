module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.BackTable

/-!
# Exception renaming, backward: the aggregate family

As for tables, most array rules read an array only through its length (`arrays_rn_back_len`).
The rules that read or write a field (`struct.get`, `struct.set`, `array.get`, `array.set`) and
the allocating rules have their own lemmas, each stated with the source code it inverts.

Refined from the earlier `Silmaril.Raw.Wasm.Models.FXRenameSim.BackAggregate`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename

variable {H : Type} {n : Nat} {s t : Store H} {f : Frame} {L : List Admin}

theorem zip_map_mem_back {α : Type} {l : List α} {vs : List Val} {Q : α → Val → Prop}
    (h : ∀ p ∈ l.zip (vs.map (rnVal n)), Q p.1 p.2) (hQ : ∀ a v, Q a (rnVal n v) → Q a v) :
    ∀ p ∈ l.zip vs, Q p.1 p.2 := by
  intro p hp
  have hp' : (p.1, rnVal n p.2) ∈ l.zip (vs.map (rnVal n)) := by
    rw [List.zip_map_right, List.mem_map]
    exact ⟨p, hp, rfl⟩
  exact hQ _ _ (h _ hp')

theorem rnStruct_fields_get_back {si : StructInst} {i : Nat} {fv : FieldVal}
    (h : (rnStruct n si).fields[i]? = some fv) :
    ∃ fv₀, si.fields[i]? = some fv₀ ∧ rnField n fv₀ = fv := by
  simpa [rnStruct] using h

theorem rnArray_fields_get_back {ai : ArrayInst} {i : Nat} {fv : FieldVal}
    (h : (rnArray n ai).fields[i]? = some fv) :
    ∃ fv₀, ai.fields[i]? = some fv₀ ∧ rnField n fv₀ = fv := by
  simpa [rnArray] using h

section Back

variable (h : ExnRen n s t)
include h

/-- A target array lookup, pulled back with its length. -/
theorem arrays_rn_back_len {a : Nat} {ai : ArrayInst} (hl : t.arrays[a]? = some ai) :
    ∃ ai₀, s.arrays[a]? = some ai₀ ∧ ai₀.fields.length = ai.fields.length := by
  obtain ⟨ai₀, ha₀, hai⟩ := arrays_rn_back h hl
  have hlen : ai₀.fields.length = ai.fields.length := by rw [← hai]; simp [rnArray]
  exact ⟨ai₀, ha₀, hlen⟩

theorem structNew_rn_back {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hn : (vs.map (rnVal n)).length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip (vs.map (rnVal n)), packable (fieldStorage p.1) p.2) :
    BackOf AggregateStep n s f (vals vs ++ [.plain (.structNew x)])
      ⟨t.addStruct ⟨d, (fs.toList.zip (vs.map (rnVal n))).map
          fun (ft, v) => packField (fieldStorage ft) v⟩,
        rnFrame n f, [.ref (.struct t.structs.length)]⟩ := by
  have hp₀ : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2 :=
    zip_map_mem_back (Q := fun ft v => packable (fieldStorage ft) v = true) hp
      (fun a v hv => by simpa only [packable_rn] using hv)
  refine backOf_intro (.structNew hd he (by simpa using hn) hp₀) ?_ (addStruct_rn h _)
  rw [structs_length h, zip_map_rn _ _ (fun ft v => packField (fieldStorage ft) v)
    (fun a v => packField_rn _ v)]
  rfl

theorem arrayNewFixed_rn_back {x : TypeIdx} {k : Fin (2 ^ 32)} {d : DefType}
    {ft : CFieldType} {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hn : (vs.map (rnVal n)).length = k.val)
    (hp : ∀ v ∈ vs.map (rnVal n), packable (fieldStorage ft) v) :
    BackOf AggregateStep n s f (vals vs ++ [.plain (.arrayNewFixed x k)])
      ⟨t.addArray ⟨d, (vs.map (rnVal n)).map (packField (fieldStorage ft))⟩, rnFrame n f,
        [arrRef t.arrays.length]⟩ := by
  have hp₀ : ∀ v ∈ vs, packable (fieldStorage ft) v := fun v hv => by
    rw [← packable_rn (n := n)]; exact hp _ (List.mem_map_of_mem hv)
  have hm : (vs.map (rnVal n)).map (packField (fieldStorage ft)) =
      (vs.map (packField (fieldStorage ft))).map (rnField n) := by
    simp only [List.map_map]
    exact List.map_congr_left fun v _ => packField_rn _ v
  refine backOf_intro (.arrayNewFixed hd he (by simpa using hn) hp₀) ?_ (addArray_rn h _)
  rw [arrays_length h, hm]
  rfl

theorem structGet_rn_back {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx} {a : Nat}
    {si : StructInst} {fv : FieldVal} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType}
    (hs : t.structs[a]? = some si) (hf : si.fields[i.toNat]? = some fv)
    (hd : (rnFrame n f).type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some ft) (hu : unpackable (fieldStorage ft) sx fv) :
    BackOf AggregateStep n s f [.ref (.struct a), .plain (.structGet sx x i)]
      ⟨t, rnFrame n f, [(unpackField sx fv).toAdmin]⟩ := by
  obtain ⟨si₀, hs₀, hsi⟩ := structs_rn_back h hs
  have hf' : (rnStruct n si₀).fields[i.toNat]? = some fv := by rw [hsi]; exact hf
  obtain ⟨fv₀, hf₀, hfv⟩ := rnStruct_fields_get_back hf'
  have hu₀ : unpackable (fieldStorage ft) sx fv₀ := by rw [← unpackable_rn (n := n), hfv]; exact hu
  refine backOf_intro (.structGetStruct hs₀ hf₀ hd he hi hu₀) ?_ h
  rw [← hfv]; rn_simp
  rw [unpackField_rn]

theorem structSet_rn_back {x : TypeIdx} {i : FieldIdx} {v : Val} {a : Nat} {d : DefType}
    {fs : Ty (.list .field)} {ft : CFieldType} {si : StructInst}
    (hd : (rnFrame n f).type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some ft) (hs : t.structs[a]? = some si)
    (hf : i.toNat < si.fields.length) (hp : packable (fieldStorage ft) (rnVal n v)) :
    BackOf AggregateStep n s f [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]
      ⟨t.setStructField a i.toNat (packField (fieldStorage ft) (rnVal n v)), rnFrame n f, []⟩ := by
  obtain ⟨si₀, hs₀, hsi⟩ := structs_rn_back h hs
  have hf₀ : i.toNat < si₀.fields.length := by simpa [← hsi, rnStruct] using hf
  have hp₀ : packable (fieldStorage ft) v := by rw [← packable_rn (n := n)]; exact hp
  refine backOf_intro (.structSetStruct hd he hi hs₀ hf₀ hp₀) ?_ (setStructField_rn h _ _ _)
  rn_simp
  rw [packField_rn]

theorem arrayGet_rn_back {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32} {a : Nat}
    {ai : ArrayInst} {fv : FieldVal} {d : DefType} {ft : CFieldType}
    (ha : t.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some fv)
    (hd : (rnFrame n f).type? x = some d) (he : Expand d (.array ft))
    (hu : unpackable (fieldStorage ft) sx fv) :
    BackOf AggregateStep n s f [arrRef a, constI32 i, .plain (.arrayGet sx x)]
      ⟨t, rnFrame n f, [(unpackField sx fv).toAdmin]⟩ := by
  obtain ⟨ai₀, ha₀, hai⟩ := arrays_rn_back h ha
  have hf' : (rnArray n ai₀).fields[i.toNat]? = some fv := by rw [hai]; exact hf
  obtain ⟨fv₀, hf₀, hfv⟩ := rnArray_fields_get_back hf'
  have hu₀ : unpackable (fieldStorage ft) sx fv₀ := by rw [← unpackable_rn (n := n), hfv]; exact hu
  refine backOf_intro (.arrayGetArray ha₀ hf₀ hd he hu₀) ?_ h
  rw [← hfv]; rn_simp
  rw [unpackField_rn]

theorem arraySet_rn_back {x : TypeIdx} {i : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst}
    {d : DefType} {ft : CFieldType} (ha : t.arrays[a]? = some ai)
    (hb : i.toNat < ai.fields.length) (hd : (rnFrame n f).type? x = some d)
    (he : Expand d (.array ft)) (hp : packable (fieldStorage ft) (rnVal n v)) :
    BackOf AggregateStep n s f [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]
      ⟨t.setArrayField a i.toNat (packField (fieldStorage ft) (rnVal n v)), rnFrame n f, []⟩ := by
  obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
  have hp₀ : packable (fieldStorage ft) v := by rw [← packable_rn (n := n)]; exact hp
  refine backOf_intro (.arraySetArray ha₀ (hl ▸ hb) hd he hp₀) ?_ (setArrayField_rn h _ _ _)
  rn_simp
  rw [packField_rn]

theorem arrayNewElem_rn_back {x : TypeIdx} {y : ElemIdx} {i k : BitVec 32} {ea : Nat}
    {ei : ElemInst} (he : t.elem? (rnFrame n f) y = some (ea, ei))
    (hb : i.toNat + k.toNat ≤ ei.refs.length) :
    BackOf AggregateStep n s f [constI32 i, constI32 k, .plain (.arrayNewElem x y)]
      ⟨t, rnFrame n f, ((ei.refs.drop i.toNat).take k.toNat).map .ref ++
        [.plain (.arrayNewFixed x ⟨k.toNat, k.isLt⟩)]⟩ := by
  obtain ⟨ei₀, he₀, hei⟩ := elem_rn_back h he
  have hb₀ : i.toNat + k.toNat ≤ ei₀.refs.length := by
    simpa [← hei, rnElem] using hb
  refine backOf_intro (.arrayNewElemAlloc he₀ hb₀) ?_ h
  rw [← hei]; rn_simp
  rw [rnAdmins_map_ref]
  simp [rnElem, List.map_drop, List.map_take]

theorem arrayInitElem_rn_back {x : TypeIdx} {y : ElemIdx} {i j k : BitVec 32} {a ea : Nat}
    {ai : ArrayInst} {ei : ElemInst} {r : Ref} (ha : t.arrays[a]? = some ai)
    (he : t.elem? (rnFrame n f) y = some (ea, ei))
    (hb : i.toNat + k.toNat ≤ ai.fields.length ∧ j.toNat + k.toNat ≤ ei.refs.length)
    (hk : k ≠ 0) (hr : ei.refs[j.toNat]? = some r) :
    BackOf AggregateStep n s f [arrRef a, constI32 i, constI32 j, constI32 k,
        .plain (.arrayInitElem x y)]
      ⟨t, rnFrame n f, [arrRef a, constI32 i, .ref r, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), constI32 (j + 1), constI32 (k - 1),
        .plain (.arrayInitElem x y)]⟩ := by
  obtain ⟨ai₀, ha₀, hla⟩ := arrays_rn_back_len h ha
  obtain ⟨ei₀, he₀, hei⟩ := elem_rn_back h he
  have hr' : (rnElem n ei₀).refs[j.toNat]? = some r := by rw [hei]; exact hr
  obtain ⟨r₀, hr₀, hrr⟩ := rnElem_refs_get_back hr'
  have hle : ei₀.refs.length = ei.refs.length := by rw [← hei]; simp [rnElem]
  have hb₀ : i.toNat + k.toNat ≤ ai₀.fields.length ∧ j.toNat + k.toNat ≤ ei₀.refs.length := by
    rw [hla, hle]; exact hb
  refine backOf_intro (.arrayInitElemSucc ha₀ he₀ hb₀ hk hr₀) ?_ h
  rw [← hrr]; rn_fin

end Back

theorem aggregate_rn_back_of (h : ExnRen n s t) {c d : Config H} (step : AggregateStep c d)
    (hc : (⟨t, rnFrame n f, rnAdmins n L⟩ : Config H) = c) : BackOf AggregateStep n s f L d := by
  cases step with
  | structNew hd he hn hp => rn_inv hc; exact structNew_rn_back h hd he hn hp
  | structNewDefault hd he hdef =>
    rn_inv hc
    refine backOf_intro (.structNewDefault hd he hdef) ?_ h
    rn_simp
    rw [map_rnVal_of_mapM _ (fun _ _ hv => rnVal_default_eq hv) _ _ hdef]
  | structGetNull => rn_inv hc; exact backOf_intro .structGetNull (by rn_fin) h
  | structGetStruct hs hf hd he hi hu => rn_inv hc; exact structGet_rn_back h hs hf hd he hi hu
  | structSetNull => rn_inv hc; exact backOf_intro .structSetNull (by rn_fin) h
  | structSetStruct hd he hi hs hf hp => rn_inv hc; exact structSet_rn_back h hd he hi hs hf hp
  | arrayNew v k =>
    rn_inv hc
    refine backOf_intro (.arrayNew _ k) ?_ h
    rn_simp
    rw [List.map_replicate]
  | arrayNewDefault hd he hv =>
    rn_inv hc
    refine backOf_intro (.arrayNewDefault hd he hv) ?_ h
    rn_simp
    rw [List.map_replicate, rnVal_default_eq hv]
  | arrayNewFixed hd he hn hp => rn_inv hc; exact arrayNewFixed_rn_back h hd he hn hp
  | arrayNewElemOob he hb =>
    rn_inv hc
    obtain ⟨ei₀, he₀, hl⟩ := elem_rn_back_len h he
    exact backOf_intro (.arrayNewElemOob he₀ (hl ▸ hb)) (by rn_fin) h
  | arrayNewElemAlloc he hb => rn_inv hc; exact arrayNewElem_rn_back h he hb
  | arrayNewDataOob hd he hdat hz hb =>
    rn_inv hc
    exact backOf_intro (.arrayNewDataOob hd he (data_rn_back h hdat) hz hb) (by rn_fin) h
  | arrayNewDataNum hd he hdat hz hb hvs =>
    rn_inv hc
    refine backOf_intro (.arrayNewDataNum hd he (data_rn_back h hdat) hz hb hvs) ?_ h
    rn_simp
    rw [map_rnVal_of_mapM _ (fun _ _ hv => rnVal_readField hv) _ _ hvs]
  | arrayGetNull => rn_inv hc; exact backOf_intro .arrayGetNull (by rn_fin) h
  | arrayGetOob ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayGetOob ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayGetArray ha hi hd he hu => rn_inv hc; exact arrayGet_rn_back h ha hi hd he hu
  | arraySetNull => rn_inv hc; exact backOf_intro .arraySetNull (by rn_fin) h
  | arraySetOob ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arraySetOob ha₀ (hl ▸ hb)) (by rn_fin) h
  | arraySetArray ha hi hd he hp => rn_inv hc; exact arraySet_rn_back h ha hi hd he hp
  | arrayLenNull => rn_inv hc; exact backOf_intro .arrayLenNull (by rn_fin) h
  | arrayLenArray ha =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayLenArray ha₀) (by rw [← hl]; rn_fin) h
  | arrayFillNull => rn_inv hc; exact backOf_intro .arrayFillNull (by rn_fin) h
  | arrayFillOob ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayFillOob ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayFillZero ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayFillZero ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayFillSucc ha hb hn =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayFillSucc ha₀ (hl ▸ hb) hn) (by rn_fin) h
  | arrayCopyNull₁ => rn_inv hc; exact backOf_intro .arrayCopyNull₁ (by rn_fin) h
  | arrayCopyNull₂ => rn_inv hc; exact backOf_intro .arrayCopyNull₂ (by rn_fin) h
  | arrayCopyOob₁ ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayCopyOob₁ ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayCopyOob₂ ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayCopyOob₂ ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayCopyZero ha₁ ha₂ hb =>
    rn_inv hc
    obtain ⟨ai₁, h₁, hl₁⟩ := arrays_rn_back_len h ha₁
    obtain ⟨ai₂, h₂, hl₂⟩ := arrays_rn_back_len h ha₂
    exact backOf_intro (.arrayCopyZero h₁ h₂ (hl₁ ▸ hl₂ ▸ hb)) (by rn_fin) h
  | arrayCopyLe ha₁ ha₂ hb hn hd he hle =>
    rn_inv hc
    obtain ⟨ai₁, h₁, hl₁⟩ := arrays_rn_back_len h ha₁
    obtain ⟨ai₂, h₂, hl₂⟩ := arrays_rn_back_len h ha₂
    exact backOf_intro (.arrayCopyLe h₁ h₂ (hl₁ ▸ hl₂ ▸ hb) hn hd he hle) (by rn_fin) h
  | arrayCopyGt ha₁ ha₂ hb hn hd he hgt =>
    rn_inv hc
    obtain ⟨ai₁, h₁, hl₁⟩ := arrays_rn_back_len h ha₁
    obtain ⟨ai₂, h₂, hl₂⟩ := arrays_rn_back_len h ha₂
    exact backOf_intro (.arrayCopyGt h₁ h₂ (hl₁ ▸ hl₂ ▸ hb) hn hd he hgt) (by rn_fin) h
  | arrayInitElemNull => rn_inv hc; exact backOf_intro .arrayInitElemNull (by rn_fin) h
  | arrayInitElemOob₁ ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayInitElemOob₁ ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayInitElemOob₂ he hb =>
    rn_inv hc
    obtain ⟨ei₀, he₀, hl⟩ := elem_rn_back_len h he
    exact backOf_intro (.arrayInitElemOob₂ he₀ (hl ▸ hb)) (by rn_fin) h
  | arrayInitElemZero ha he hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hla⟩ := arrays_rn_back_len h ha
    obtain ⟨ei₀, he₀, hle⟩ := elem_rn_back_len h he
    exact backOf_intro (.arrayInitElemZero ha₀ he₀ (hla ▸ hle ▸ hb)) (by rn_fin) h
  | arrayInitElemSucc ha he hb hn hr => rn_inv hc; exact arrayInitElem_rn_back h ha he hb hn hr
  | arrayInitDataNull => rn_inv hc; exact backOf_intro .arrayInitDataNull (by rn_fin) h
  | arrayInitDataOob₁ ha hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayInitDataOob₁ ha₀ (hl ▸ hb)) (by rn_fin) h
  | arrayInitDataOob₂ hd he hdat hz hb =>
    rn_inv hc
    exact backOf_intro (.arrayInitDataOob₂ hd he (data_rn_back h hdat) hz hb) (by rn_fin) h
  | arrayInitDataZero ha hdat hb =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    exact backOf_intro (.arrayInitDataZero ha₀ (data_rn_back h hdat) (hl ▸ hb)) (by rn_fin) h
  | arrayInitDataNum ha hd he hdat hb hn hv =>
    rn_inv hc
    obtain ⟨ai₀, ha₀, hl⟩ := arrays_rn_back_len h ha
    refine backOf_intro (.arrayInitDataNum ha₀ hd he (data_rn_back h hdat) (hl ▸ hb) hn hv) ?_ h
    rn_simp
    rw [rnVal_readField hv]

theorem aggregate_rn_back (h : ExnRen n s t) {d : Config H}
    (step : AggregateStep ⟨t, rnFrame n f, rnAdmins n L⟩ d) : BackOf AggregateStep n s f L d :=
  aggregate_rn_back_of h step rfl

end Silmaril.Proofs.Wasm.Models.FXRenameSim
