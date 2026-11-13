module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Leaf

/-!
# Exception renaming: the aggregate family

Each rule of `AggregateStep` is matched, under `ExnRen n s t`, by the same rule on the renamed
configuration. Structures and arrays hold renamed fields: packing and unpacking commute with the
renaming (`packField_rn`, `unpackField_rn`, with the same domains), default values and values
read from data segments are not references, so the renaming fixes them (`mapM_default_rn`,
`mapM_readField_rn`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename

variable {H : Type} {n : Nat} {s t s' : Store H} {f f' : Frame} {code out : List Admin}

theorem packField_rn (zt : CStorageType) (v : Val) :
    packField zt (rnVal n v) = rnField n (packField zt v) := by
  rcases v with ⟨⟨it | ft⟩, b⟩ | b | r <;> cases zt <;> rfl

theorem packable_rn (zt : CStorageType) (v : Val) : packable zt (rnVal n v) = packable zt v := by
  rcases v with ⟨⟨it | ft⟩, b⟩ | b | r <;> cases zt <;> rfl

theorem unpackField_rn (sx : Option Signedness) (fv : FieldVal) :
    unpackField sx (rnField n fv) = rnVal n (unpackField sx fv) := by
  cases fv with
  | val v => rfl
  | pack p b => rcases sx with _ | ⟨_ | _⟩ <;> rfl

theorem unpackable_rn (zt : CStorageType) (sx : Option Signedness) (fv : FieldVal) :
    unpackable zt sx (rnField n fv) = unpackable zt sx fv := by
  cases fv <;> cases zt <;> rcases sx with _ | ⟨_ | _⟩ <;> rfl

theorem rnVal_default_eq {ct : CValType} {v : Val} (h : defaultVal? ct = some v) : rnVal n v = v := by
  unfold defaultVal? at h
  split at h <;> cases h <;> rfl

theorem rnVal_readField {zt : CStorageType} {bs : ByteArray} {off : Nat} {v : Val}
    (h : readField? zt bs off = some v) : rnVal n v = v := by
  unfold readField? at h
  split at h
  all_goals first
    | (rw [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl)
    | cases h

theorem map_rnVal_of_mapM {α : Type} (g : α → Option Val) (hg : ∀ a v, g a = some v → rnVal n v = v) :
    ∀ (l : List α) (vs : List Val), l.mapM g = some vs → vs.map (rnVal n) = vs
  | [], vs, h => by simp at h; subst h; rfl
  | a :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    rw [List.map_cons, hg a v hv, map_rnVal_of_mapM g hg l ws hws]

theorem zip_map_rn {α : Type} (l : List α) (vs : List Val) (F : α → Val → FieldVal)
    (hF : ∀ a v, F a (rnVal n v) = rnField n (F a v)) :
    (l.zip (vs.map (rnVal n))).map (fun p => F p.1 p.2) =
      ((l.zip vs).map (fun p => F p.1 p.2)).map (rnField n) := by
  induction l generalizing vs with
  | nil => simp
  | cons a l ih =>
    cases vs with
    | nil => simp
    | cons v vs => simp [hF, ih]

theorem zip_map_mem {α : Type} {l : List α} {vs : List Val} {Q : α → Val → Prop}
    (h : ∀ p ∈ l.zip vs, Q p.1 p.2) (hQ : ∀ a v, Q a v → Q a (rnVal n v)) :
    ∀ p ∈ l.zip (vs.map (rnVal n)), Q p.1 p.2 := by
  intro p hp
  rw [List.zip_map_right, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hQ _ _ (h q hq)

theorem structs_length (h : ExnRen n s t) : t.structs.length = s.structs.length := by
  rw [h.structs, List.length_map]

theorem arrays_length (h : ExnRen n s t) : t.arrays.length = s.arrays.length := by
  rw [h.arrays, List.length_map]

@[simp] theorem rnArray_fields_length (ai : ArrayInst) :
    (rnArray n ai).fields.length = ai.fields.length := by
  simp [rnArray]

theorem rnAdmins_map_ref (l : List Ref) :
    rnAdmins n (l.map Admin.ref) = (l.map (rnRef n)).map Admin.ref := by
  induction l with
  | nil => rfl
  | cons r l ih => simp [ih]

theorem structNew_rn (h : ExnRen n s t) {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
    AggregateStep ⟨t, rnFrame n f, rnAdmins n (vals vs ++ [.plain (.structNew x)])⟩
      ⟨t.addStruct (rnStruct n
          ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩),
        rnFrame n f, rnAdmins n [.ref (.struct s.structs.length)]⟩ := by
  have hs := AggregateStep.structNew (s := t) (f := rnFrame n f) (vs := vs.map (rnVal n)) hd he
    (by simpa using hn)
    (zip_map_mem (Q := fun ft v => packable (fieldStorage ft) v = true) hp
      (fun a v hv => by rwa [packable_rn]))
  rw [structs_length h, zip_map_rn _ _ (fun ft v => packField (fieldStorage ft) v)
    (fun a v => packField_rn _ v)] at hs
  rn_simp
  exact hs

theorem arrayNewFixed_rn (h : ExnRen n s t) {x : TypeIdx} {k : Fin (2 ^ 32)} {d : DefType}
    {ft : CFieldType} {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hn : vs.length = k.val) (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
    AggregateStep ⟨t, rnFrame n f, rnAdmins n (vals vs ++ [.plain (.arrayNewFixed x k)])⟩
      ⟨t.addArray (rnArray n ⟨d, vs.map (packField (fieldStorage ft))⟩), rnFrame n f,
        rnAdmins n [arrRef s.arrays.length]⟩ := by
  have hp' : ∀ v ∈ vs.map (rnVal n), packable (fieldStorage ft) v := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [packable_rn]; exact hp w hw
  have hm : (vs.map (rnVal n)).map (packField (fieldStorage ft)) =
      (vs.map (packField (fieldStorage ft))).map (rnField n) := by
    simp only [List.map_map]
    exact List.map_congr_left fun v _ => packField_rn _ v
  have ha := AggregateStep.arrayNewFixed (s := t) (f := rnFrame n f) (vs := vs.map (rnVal n))
    hd he (by simpa using hn) hp'
  rw [arrays_length h, hm] at ha
  rn_simp
  exact ha

theorem arrayNewElemAlloc_rn (h : ExnRen n s t) {x : TypeIdx} {y : ElemIdx} {i k : BitVec 32}
    {ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
    (hb : i.toNat + k.toNat ≤ ei.refs.length) :
    AggregateStep ⟨t, rnFrame n f, rnAdmins n [constI32 i, constI32 k, .plain (.arrayNewElem x y)]⟩
      ⟨t, rnFrame n f, rnAdmins n (((ei.refs.drop i.toNat).take k.toNat).map .ref ++
          [.plain (.arrayNewFixed x ⟨k.toNat, k.isLt⟩)])⟩ := by
  have hs := AggregateStep.arrayNewElemAlloc (x := x) (elem_rn h he) (by simpa using hb)
  rn_simp
  rw [rnAdmins_map_ref]
  simpa [rnElem, List.map_drop, List.map_take] using hs

theorem arrayLenArray_rn (h : ExnRen n s t) {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) :
    AggregateStep ⟨t, rnFrame n f, rnAdmins n [arrRef a, .plain .arrayLen]⟩
      ⟨t, rnFrame n f, rnAdmins n [constI32 (BitVec.ofNat 32 ai.fields.length)]⟩ := by
  have hs := AggregateStep.arrayLenArray (f := rnFrame n f) (arrays_rn h ha)
  rn_simp
  simpa using hs

theorem aggregate_rn (h : ExnRen n s t) (step : AggregateStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    ∃ t', AggregateStep ⟨t, rnFrame n f, rnAdmins n code⟩ ⟨t', rnFrame n f', rnAdmins n out⟩ ∧
      ExnRen n s' t' := by
  cases step with
  | structNew hd he hn hp => exact ⟨_, structNew_rn h hd he hn hp, addStruct_rn h _⟩
  | structNewDefault hd he hdef =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [map_rnVal_of_mapM _ (fun _ _ hv => rnVal_default_eq hv) _ _ hdef]
    exact .structNewDefault hd he hdef
  | structGetNull => exact ⟨t, .structGetNull, h⟩
  | structGetStruct hs hf hd he hi hu =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [← unpackField_rn]
    exact .structGetStruct (structs_rn h hs) (by simp [rnStruct, hf]) hd he hi
      (by rwa [unpackable_rn])
  | structSetNull => refine ⟨t, ?_, h⟩; rn_simp; exact .structSetNull
  | structSetStruct hd he hi hs hf hp =>
    refine ⟨_, ?_, setStructField_rn h _ _ _⟩
    rn_simp
    rw [← packField_rn]
    exact .structSetStruct hd he hi (structs_rn h hs) (by simpa [rnStruct] using hf)
      (by rwa [packable_rn])
  | arrayNew v k =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [List.map_replicate]
    exact .arrayNew _ k
  | arrayNewDefault hd he hv =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [List.map_replicate, rnVal_default_eq hv]
    exact .arrayNewDefault hd he hv
  | arrayNewFixed hd he hn hp => exact ⟨_, arrayNewFixed_rn h hd he hn hp, addArray_rn h _⟩
  | arrayNewElemOob he hb =>
    exact ⟨t, .arrayNewElemOob (elem_rn h he) (by simpa using hb), h⟩
  | arrayNewElemAlloc he hb => exact ⟨t, arrayNewElemAlloc_rn h he hb, h⟩
  | arrayNewDataOob hd he hdat hz hb =>
    exact ⟨t, .arrayNewDataOob hd he (data_rn h hdat) hz hb, h⟩
  | arrayNewDataNum hd he hdat hz hb hvs =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [map_rnVal_of_mapM _ (fun _ _ hv => rnVal_readField hv) _ _ hvs]
    exact .arrayNewDataNum hd he (data_rn h hdat) hz hb hvs
  | arrayGetNull => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayGetNull
  | arrayGetOob ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayGetOob (arrays_rn h ha) (by simpa using hb)
  | arrayGetArray ha hi hd he hu =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [← unpackField_rn]
    exact .arrayGetArray (arrays_rn h ha) (by simp [rnArray, hi]) hd he (by rwa [unpackable_rn])
  | arraySetNull => refine ⟨t, ?_, h⟩; rn_simp; exact .arraySetNull
  | arraySetOob ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arraySetOob (arrays_rn h ha) (by simpa using hb)
  | arraySetArray ha hi hd he hp =>
    refine ⟨_, ?_, setArrayField_rn h _ _ _⟩
    rn_simp
    rw [← packField_rn]
    exact .arraySetArray (arrays_rn h ha) (by simpa using hi) hd he (by rwa [packable_rn])
  | arrayLenNull => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayLenNull
  | arrayLenArray ha => exact ⟨t, arrayLenArray_rn h ha, h⟩
  | arrayFillNull => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayFillNull
  | arrayFillOob ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayFillOob (arrays_rn h ha) (by simpa using hb)
  | arrayFillZero ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayFillZero (arrays_rn h ha) (by simpa using hb)
  | arrayFillSucc ha hb hn =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayFillSucc (arrays_rn h ha) (by simpa using hb) hn
  | arrayCopyNull₁ => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayCopyNull₁
  | arrayCopyNull₂ => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayCopyNull₂
  | arrayCopyOob₁ ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayCopyOob₁ (arrays_rn h ha) (by simpa using hb)
  | arrayCopyOob₂ ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayCopyOob₂ (arrays_rn h ha) (by simpa using hb)
  | arrayCopyZero ha₁ ha₂ hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayCopyZero (arrays_rn h ha₁) (arrays_rn h ha₂) (by simpa using hb)
  | arrayCopyLe ha₁ ha₂ hb hn hd he hle =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayCopyLe (arrays_rn h ha₁) (arrays_rn h ha₂) (by simpa using hb) hn hd he hle
  | arrayCopyGt ha₁ ha₂ hb hn hd he hgt =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayCopyGt (arrays_rn h ha₁) (arrays_rn h ha₂) (by simpa using hb) hn hd he hgt
  | arrayInitElemNull => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayInitElemNull
  | arrayInitElemOob₁ ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitElemOob₁ (arrays_rn h ha) (by simpa using hb)
  | arrayInitElemOob₂ he hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitElemOob₂ (elem_rn h he) (by simpa using hb)
  | arrayInitElemZero ha he hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitElemZero (arrays_rn h ha) (elem_rn h he) (by simpa using hb)
  | arrayInitElemSucc ha he hb hn hr =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitElemSucc (arrays_rn h ha) (elem_rn h he) (by simpa using hb) hn
      (rnElem_refs_get hr)
  | arrayInitDataNull => refine ⟨t, ?_, h⟩; rn_simp; exact .arrayInitDataNull
  | arrayInitDataOob₁ ha hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitDataOob₁ (arrays_rn h ha) (by simpa using hb)
  | arrayInitDataOob₂ hd he hdat hz hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitDataOob₂ hd he (data_rn h hdat) hz hb
  | arrayInitDataZero ha hdat hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .arrayInitDataZero (arrays_rn h ha) (data_rn h hdat) (by simpa using hb)
  | arrayInitDataNum ha hd he hdat hb hn hv =>
    refine ⟨t, ?_, h⟩; rn_simp
    rw [rnVal_readField hv]
    exact .arrayInitDataNum (arrays_rn h ha) hd he (data_rn h hdat) (by simpa using hb) hn hv

end Silmaril.Proofs.Wasm.Models.FXRenameSim
