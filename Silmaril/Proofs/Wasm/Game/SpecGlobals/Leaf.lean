module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Basic

/-!
# Leaf reductions under global-address embeddings

Every variable, reference, aggregate, table and memory leaf rule transports through a
global-address embedding `Emb ρ D` (`Silmaril.Proofs.Wasm.Game.SpecGlobals.Basic`): the same
code, the same runtime output, exact allocations and updates. Global accesses go through a
frame naming globals in `D` (`ModDom`), reference tests through `Emb.refOk_iff`. Leaf rules
keep the frame's module and produce code without frames.

Source: the aggregate, table and memory cases are copied from silmaril-lean's
`Silmaril/Wasm/Link/GlobalRenameLeaf.lean` (pinned revision
35a6f60ab146faef38970ec99e7399a0764dee82), with the permutation replaced by an embedding;
the variable and reference cases adapt `variable_step`/`reference_step` of
`Silmaril/Wasm/Link/GlobalPermutation.lean`. The frame and code facts are new.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}


theorem type_lookup {ρ : Nat → Nat} {f : Frame}
    {x : TypeIdx} {d : DefType} (h : f.type? x = some d) :
    (frame ρ f).type? x = some d := by
  simpa only [Frame.type?, frame, moduleView] using h

theorem table_lookup {ρ : Nat → Nat} {D : Nat → Prop} {source target : Store H} {f : Frame}
    (stores : Emb ρ D source target)
    {x : TableIdx} {a : Nat} {ti : TableInst} (h : source.table? f x = some (a, ti)) :
    target.table? (frame ρ f) x = some (a, ti) := by
  simpa only [Store.table?, frame, moduleView, ← stores.tables] using h

theorem elem_lookup {ρ : Nat → Nat} {D : Nat → Prop} {source target : Store H} {f : Frame}
    (stores : Emb ρ D source target)
    {x : ElemIdx} {a : Nat} {ei : ElemInst} (h : source.elem? f x = some (a, ei)) :
    target.elem? (frame ρ f) x = some (a, ei) := by
  simpa only [Store.elem?, frame, moduleView, ← stores.elems] using h

theorem mem_lookup {ρ : Nat → Nat} {D : Nat → Prop} {source target : Store H} {f : Frame}
    (stores : Emb ρ D source target)
    {x : MemIdx} {a : Nat} {mi : MemInst} (h : source.mem? f x = some (a, mi)) :
    target.mem? (frame ρ f) x = some (a, mi) := by
  simpa only [Store.mem?, frame, moduleView, ← stores.mems] using h

theorem data_lookup {ρ : Nat → Nat} {D : Nat → Prop} {source target : Store H} {f : Frame}
    (stores : Emb ρ D source target)
    {x : DataIdx} {a : Nat} {di : DataInst} (h : source.data? f x = some (a, di)) :
    target.data? (frame ρ f) x = some (a, di) := by
  simpa only [Store.data?, frame, moduleView, ← stores.datas] using h

/-- All aggregate rules transport their exact GC allocations, updates and
bulk-operation expansions through global address renaming. -/
theorem aggregate_step {ρ : Nat → Nat} {D : Nat → Prop} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (stores : Emb ρ D source target)
    (step : AggregateStep ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', AggregateStep ⟨target, frame ρ f, code⟩ ⟨target', frame ρ f', out⟩ ∧
      Emb ρ D source' target' := by
  cases step with
  | structNew hd he hn hp =>
    exact ⟨_, by simpa only [stores.structs] using
      AggregateStep.structNew (s := target) (type_lookup hd) he hn hp,
      stores.addStruct _⟩
  | structNewDefault hd he hv =>
    exact ⟨_, .structNewDefault (type_lookup hd) he hv, stores⟩
  | structGetNull => exact ⟨_, .structGetNull, stores⟩
  | structGetStruct hs hf hd he hi hu =>
    exact ⟨_, .structGetStruct (stores.structs ▸ hs) hf (type_lookup hd) he hi hu, stores⟩
  | structSetNull => exact ⟨_, .structSetNull, stores⟩
  | structSetStruct hd he hi hs hf hp =>
    exact ⟨_, .structSetStruct (type_lookup hd) he hi (stores.structs ▸ hs) hf hp,
      stores.setStructField _ _ _⟩
  | arrayNew v n => exact ⟨_, .arrayNew v n, stores⟩
  | arrayNewDefault hd he hv =>
    exact ⟨_, .arrayNewDefault (type_lookup hd) he hv, stores⟩
  | arrayNewFixed hd he hn hp =>
    exact ⟨_, by simpa only [stores.arrays] using
      AggregateStep.arrayNewFixed (s := target) (type_lookup hd) he hn hp,
      stores.addArray _⟩
  | arrayNewElemOob he hb => exact ⟨_, .arrayNewElemOob (elem_lookup stores he) hb, stores⟩
  | arrayNewElemAlloc he hb => exact ⟨_, .arrayNewElemAlloc (elem_lookup stores he) hb, stores⟩
  | arrayNewDataOob hd he ht hz hb =>
    exact ⟨_, .arrayNewDataOob (type_lookup hd) he (data_lookup stores ht) hz hb, stores⟩
  | arrayNewDataNum hd he ht hz hb hv =>
    exact ⟨_, .arrayNewDataNum (type_lookup hd) he (data_lookup stores ht) hz hb hv, stores⟩
  | arrayGetNull => exact ⟨_, .arrayGetNull, stores⟩
  | arrayGetOob ha hb => exact ⟨_, .arrayGetOob (stores.arrays ▸ ha) hb, stores⟩
  | arrayGetArray ha hi hd he hu =>
    exact ⟨_, .arrayGetArray (stores.arrays ▸ ha) hi (type_lookup hd) he hu, stores⟩
  | arraySetNull => exact ⟨_, .arraySetNull, stores⟩
  | arraySetOob ha hb => exact ⟨_, .arraySetOob (stores.arrays ▸ ha) hb, stores⟩
  | arraySetArray ha hi hd he hp =>
    exact ⟨_, .arraySetArray (stores.arrays ▸ ha) hi (type_lookup hd) he hp,
      stores.setArrayField _ _ _⟩
  | arrayLenNull => exact ⟨_, .arrayLenNull, stores⟩
  | arrayLenArray ha => exact ⟨_, .arrayLenArray (stores.arrays ▸ ha), stores⟩
  | arrayFillNull => exact ⟨_, .arrayFillNull, stores⟩
  | arrayFillOob ha hb => exact ⟨_, .arrayFillOob (stores.arrays ▸ ha) hb, stores⟩
  | arrayFillZero ha hb => exact ⟨_, .arrayFillZero (stores.arrays ▸ ha) hb, stores⟩
  | arrayFillSucc ha hb hn => exact ⟨_, .arrayFillSucc (stores.arrays ▸ ha) hb hn, stores⟩
  | arrayCopyNull₁ => exact ⟨_, .arrayCopyNull₁, stores⟩
  | arrayCopyNull₂ => exact ⟨_, .arrayCopyNull₂, stores⟩
  | arrayCopyOob₁ ha hb => exact ⟨_, .arrayCopyOob₁ (stores.arrays ▸ ha) hb, stores⟩
  | arrayCopyOob₂ ha hb => exact ⟨_, .arrayCopyOob₂ (stores.arrays ▸ ha) hb, stores⟩
  | arrayCopyZero ha₁ ha₂ hb =>
    exact ⟨_, .arrayCopyZero (stores.arrays ▸ ha₁) (stores.arrays ▸ ha₂) hb, stores⟩
  | arrayCopyLe ha₁ ha₂ hb hn hd he hl =>
    exact ⟨_, .arrayCopyLe (stores.arrays ▸ ha₁) (stores.arrays ▸ ha₂) hb hn
      (type_lookup hd) he hl, stores⟩
  | arrayCopyGt ha₁ ha₂ hb hn hd he hl =>
    exact ⟨_, .arrayCopyGt (stores.arrays ▸ ha₁) (stores.arrays ▸ ha₂) hb hn
      (type_lookup hd) he hl, stores⟩
  | arrayInitElemNull => exact ⟨_, .arrayInitElemNull, stores⟩
  | arrayInitElemOob₁ ha hb => exact ⟨_, .arrayInitElemOob₁ (stores.arrays ▸ ha) hb, stores⟩
  | arrayInitElemOob₂ he hb => exact ⟨_, .arrayInitElemOob₂ (elem_lookup stores he) hb, stores⟩
  | arrayInitElemZero ha he hb =>
    exact ⟨_, .arrayInitElemZero (stores.arrays ▸ ha) (elem_lookup stores he) hb, stores⟩
  | arrayInitElemSucc ha he hb hn hr =>
    exact ⟨_, .arrayInitElemSucc (stores.arrays ▸ ha) (elem_lookup stores he) hb hn hr, stores⟩
  | arrayInitDataNull => exact ⟨_, .arrayInitDataNull, stores⟩
  | arrayInitDataOob₁ ha hb => exact ⟨_, .arrayInitDataOob₁ (stores.arrays ▸ ha) hb, stores⟩
  | arrayInitDataOob₂ hd he ht hz hb =>
    exact ⟨_, .arrayInitDataOob₂ (type_lookup hd) he (data_lookup stores ht) hz hb, stores⟩
  | arrayInitDataZero ha ht hb =>
    exact ⟨_, .arrayInitDataZero (stores.arrays ▸ ha) (data_lookup stores ht) hb, stores⟩
  | arrayInitDataNum ha hd he ht hb hn hv =>
    exact ⟨_, .arrayInitDataNum (stores.arrays ▸ ha) (type_lookup hd) he
      (data_lookup stores ht) hb hn hv, stores⟩

/-- Table accesses, growth, bulk expansion and element drop retain the same
operands, policy and exact store mutation under global address renaming. -/
theorem table_step {ρ : Nat → Nat} {D : Nat → Prop} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (stores : Emb ρ D source target)
    (h : TableStep P ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', TableStep P ⟨target, frame ρ f, code⟩ ⟨target', frame ρ f', out⟩ ∧
      Emb ρ D source' target' := by
  cases h with
  | getOob ht h => exact ⟨target,.getOob (table_lookup stores ht) h,stores⟩
  | getVal ht h => exact ⟨target,.getVal (table_lookup stores ht) h,stores⟩
  | setOob ht h => exact ⟨target,.setOob (table_lookup stores ht) h,stores⟩
  | setVal ht h => exact ⟨_,.setVal (table_lookup stores ht) h,stores.setTable _ _⟩
  | size ht => exact ⟨target,.size (table_lookup stores ht),stores⟩
  | growSucceed ht hg hp => exact ⟨_,.growSucceed (table_lookup stores ht) hg hp,stores.setTable _ _⟩
  | growFail ht hp => exact ⟨target,.growFail (table_lookup stores ht) hp,stores⟩
  | fillOob ht h => exact ⟨target,.fillOob (table_lookup stores ht) h,stores⟩
  | fillZero ht h => exact ⟨target,.fillZero (table_lookup stores ht) h,stores⟩
  | fillSucc ht h hn => exact ⟨target,.fillSucc (table_lookup stores ht) h hn,stores⟩
  | copyOob h₁ h₂ h => exact ⟨target,.copyOob (table_lookup stores h₁) (table_lookup stores h₂) h,stores⟩
  | copyZero h₁ h₂ h => exact ⟨target,.copyZero (table_lookup stores h₁) (table_lookup stores h₂) h,stores⟩
  | copyLe h₁ h₂ h hn hle => exact ⟨target,.copyLe (table_lookup stores h₁) (table_lookup stores h₂) h hn hle,stores⟩
  | copyGt h₁ h₂ h hn hgt => exact ⟨target,.copyGt (table_lookup stores h₁) (table_lookup stores h₂) h hn hgt,stores⟩
  | initOob ht he h => exact ⟨target,.initOob (table_lookup stores ht) (elem_lookup stores he) h,stores⟩
  | initZero ht he h => exact ⟨target,.initZero (table_lookup stores ht) (elem_lookup stores he) h,stores⟩
  | initSucc ht he h hn hr => exact ⟨target,.initSucc (table_lookup stores ht) (elem_lookup stores he) h hn hr,stores⟩
  | elemDrop he => exact ⟨_,.elemDrop (elem_lookup stores he),stores.setElem _ []⟩

/-- Scalar/vector loads and stores, growth, bulk-memory expansion and data
drop commute with the permutation of global addresses. -/
theorem memory_step {ρ : Nat → Nat} {D : Nat → Prop} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (stores : Emb ρ D source target)
    (h : MemoryStep P ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', MemoryStep P ⟨target, frame ρ f, code⟩ ⟨target', frame ρ f', out⟩ ∧
      Emb ρ D source' target' := by
  cases h with
  | loadIntOob hm h => exact ⟨target,.loadIntOob (mem_lookup stores hm) h,stores⟩
  | loadIntVal hm hl => exact ⟨target,.loadIntVal (mem_lookup stores hm) hl,stores⟩
  | loadPackOob hm h => exact ⟨target,.loadPackOob (mem_lookup stores hm) h,stores⟩
  | loadPackVal hm hl => exact ⟨target,.loadPackVal (mem_lookup stores hm) hl,stores⟩
  | loadFloatOob hm h => exact ⟨target,.loadFloatOob (mem_lookup stores hm) h,stores⟩
  | loadFloatVal hm hl => exact ⟨target,.loadFloatVal (mem_lookup stores hm) hl,stores⟩
  | vecLoadOob hm h => exact ⟨target,.vecLoadOob (mem_lookup stores hm) h,stores⟩
  | vecLoadVal hm hl => exact ⟨target,.vecLoadVal (mem_lookup stores hm) hl,stores⟩
  | vecLoadLaneOob hm h => exact ⟨target,.vecLoadLaneOob (mem_lookup stores hm) h,stores⟩
  | vecLoadLaneVal hm hl => exact ⟨target,.vecLoadLaneVal (mem_lookup stores hm) hl,stores⟩
  | storeIntOob hm h => exact ⟨target,.storeIntOob (mem_lookup stores hm) h,stores⟩
  | storeIntVal hm hs => exact ⟨_,.storeIntVal (mem_lookup stores hm) hs,stores.setMem _ _⟩
  | storePackOob hm h => exact ⟨target,.storePackOob (mem_lookup stores hm) h,stores⟩
  | storePackVal hm hs => exact ⟨_,.storePackVal (mem_lookup stores hm) hs,stores.setMem _ _⟩
  | storeFloatOob hm h => exact ⟨target,.storeFloatOob (mem_lookup stores hm) h,stores⟩
  | storeFloatVal hm hs => exact ⟨_,.storeFloatVal (mem_lookup stores hm) hs,stores.setMem _ _⟩
  | vecStoreOob hm h => exact ⟨target,.vecStoreOob (mem_lookup stores hm) h,stores⟩
  | vecStoreVal hm hs => exact ⟨_,.vecStoreVal (mem_lookup stores hm) hs,stores.setMem _ _⟩
  | vecStoreLaneOob hm h => exact ⟨target,.vecStoreLaneOob (mem_lookup stores hm) h,stores⟩
  | vecStoreLaneVal hm hs => exact ⟨_,.vecStoreLaneVal (mem_lookup stores hm) hs,stores.setMem _ _⟩
  | size hm => exact ⟨target,.size (mem_lookup stores hm),stores⟩
  | growSucceed hm hg hp => exact ⟨_,.growSucceed (mem_lookup stores hm) hg hp,stores.setMem _ _⟩
  | growFail hm hp => exact ⟨target,.growFail (mem_lookup stores hm) hp,stores⟩
  | fillOob hm h => exact ⟨target,.fillOob (mem_lookup stores hm) h,stores⟩
  | fillZero hm h => exact ⟨target,.fillZero (mem_lookup stores hm) h,stores⟩
  | fillSucc hm h hn => exact ⟨target,.fillSucc (mem_lookup stores hm) h hn,stores⟩
  | copyOob h₁ h₂ h => exact ⟨target,.copyOob (mem_lookup stores h₁) (mem_lookup stores h₂) h,stores⟩
  | copyZero h₁ h₂ h => exact ⟨target,.copyZero (mem_lookup stores h₁) (mem_lookup stores h₂) h,stores⟩
  | copyLe h₁ h₂ h hn hle => exact ⟨target,.copyLe (mem_lookup stores h₁) (mem_lookup stores h₂) h hn hle,stores⟩
  | copyGt h₁ h₂ h hn hgt => exact ⟨target,.copyGt (mem_lookup stores h₁) (mem_lookup stores h₂) h hn hgt,stores⟩
  | initOob hm hd h => exact ⟨target,.initOob (mem_lookup stores hm) (data_lookup stores hd) h,stores⟩
  | initZero hm hd h => exact ⟨target,.initZero (mem_lookup stores hm) (data_lookup stores hd) h,stores⟩
  | initSucc hm hd h hn hb => exact ⟨target,.initSucc (mem_lookup stores hm) (data_lookup stores hd) h hn hb,stores⟩
  | dataDrop hd => exact ⟨_,.dataDrop (data_lookup stores hd),stores.setData _ _⟩



/-- Variable rules transport through an embedding, given a frame naming globals in `D`. -/
theorem variable_step {ρ : Nat → Nat} {D : Nat → Prop} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (h : Emb ρ D source target) (hf : ModDom D f.module)
    (step : VariableStep ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', VariableStep ⟨target, frame ρ f, code⟩ ⟨target', frame ρ f', out⟩ ∧
      Emb ρ D source' target' := by
  cases step with
  | localGet lookup => exact ⟨target, .localGet lookup, h⟩
  | localSet bound => exact ⟨target, .localSet bound, h⟩
  | localTee => exact ⟨target, .localTee, h⟩
  | globalGet lookup => exact ⟨target, .globalGet (h.global_lookup hf lookup).1, h⟩
  | @globalSet _ _ x address g value lookup =>
    obtain ⟨hl, hd⟩ := h.global_lookup hf lookup
    exact ⟨target.setGlobal (ρ address) value, .globalSet hl, h.setGlobal hd value⟩

/-- Reference rules observe unchanged tags and GC objects and equal function types. -/
theorem reference_step {ρ : Nat → Nat} {D : Nat → Prop} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (h : Emb ρ D source target)
    (step : RefStep ⟨source, f, code⟩ ⟨source', f', out⟩) :
    source' = source ∧ RefStep ⟨target, frame ρ f, code⟩ ⟨target, frame ρ f', out⟩ := by
  cases step with
  | refNull ht => exact ⟨rfl, .refNull ht⟩
  | refFunc hf => exact ⟨rfl, .refFunc hf⟩
  | refI31 bits => exact ⟨rfl, .refI31 bits⟩
  | isNullTrue => exact ⟨rfl, .isNullTrue⟩
  | isNullFalse hn => exact ⟨rfl, .isNullFalse hn⟩
  | asNonNullNull => exact ⟨rfl, .asNonNullNull⟩
  | asNonNullAddr hn => exact ⟨rfl, .asNonNullAddr hn⟩
  | eqNull => exact ⟨rfl, .eqNull⟩
  | eqTrue hn => exact ⟨rfl, .eqTrue hn⟩
  | eqFalse hn => exact ⟨rfl, .eqFalse hn⟩
  | testTrue valid => exact ⟨rfl, .testTrue (h.refOk valid)⟩
  | testFalse invalid => exact ⟨rfl, .testFalse (fun valid => invalid (h.refOk_back valid))⟩
  | castSucceed valid => exact ⟨rfl, .castSucceed (h.refOk valid)⟩
  | castFail invalid => exact ⟨rfl, .castFail (fun valid => invalid (h.refOk_back valid))⟩
  | i31GetNull sign => exact ⟨rfl, .i31GetNull sign⟩
  | i31GetNum sign bits => exact ⟨rfl, .i31GetNum sign bits⟩
  | externConvertNull => exact ⟨rfl, .externConvertNull⟩
  | externConvertAddr hn => exact ⟨rfl, .externConvertAddr hn⟩
  | anyConvertNull => exact ⟨rfl, .anyConvertNull⟩
  | anyConvertAddr r => exact ⟨rfl, .anyConvertAddr r⟩

/-! ## Frames and code of leaf rules -/

theorem variable_frame {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : VariableStep ⟨s, f, code⟩ ⟨s', f', out⟩) : f'.module = f.module := by
  cases step <;> rfl

theorem reference_frame {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : RefStep ⟨s, f, code⟩ ⟨s', f', out⟩) : f' = f := by
  cases step <;> rfl

theorem aggregate_frame {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : AggregateStep ⟨s, f, code⟩ ⟨s', f', out⟩) : f' = f := by
  cases step <;> rfl

theorem table_frame {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : TableStep P ⟨s, f, code⟩ ⟨s', f', out⟩) : f' = f := by
  cases step <;> rfl

theorem memory_frame {s s' : Store H} {f f' : Frame} {code out : List Admin}
    (step : MemoryStep P ⟨s, f, code⟩ ⟨s', f', out⟩) : f' = f := by
  cases step <;> rfl

theorem variable_code {ρ : Nat → Nat} {D : Nat → Prop} {s s' : Store H} {f f' : Frame}
    {code out : List Admin} (step : VariableStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    admins ρ code = code ∧ admins ρ out = out ∧ AdminsDom D out := by
  cases step <;> simp only [admins, admin, admin_value, adminsDom_cons, adminsDom_nil,
    adminDom_value, adminDom_plain, and_self]

theorem reference_code {ρ : Nat → Nat} {D : Nat → Prop} {s s' : Store H} {f f' : Frame}
    {code out : List Admin} (step : RefStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    admins ρ code = code ∧ admins ρ out = out ∧ AdminsDom D out := by
  cases step <;> simp only [admins, admin, admin_value, constI32, adminsDom_cons, adminsDom_nil,
    adminDom_value, adminDom_ref, adminDom_trap, and_self]

theorem aggregate_code {ρ : Nat → Nat} {D : Nat → Prop} {s s' : Store H} {f f' : Frame}
    {code out : List Admin} (step : AggregateStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    admins ρ code = code ∧ admins ρ out = out ∧ AdminsDom D out := by
  cases step <;> simp only [admins_append, admins_vals, admins_refs, admins, admin, admin_value,
    constI32, adminsDom_cons, adminsDom_nil, adminsDom_append, adminsDom_vals, adminsDom_refs,
    adminDom_value, adminDom_plain, adminDom_ref, adminDom_trap, and_self]

theorem table_code {ρ : Nat → Nat} {D : Nat → Prop} {s s' : Store H} {f f' : Frame}
    {code out : List Admin} (step : TableStep P ⟨s, f, code⟩ ⟨s', f', out⟩) :
    admins ρ code = code ∧ admins ρ out = out ∧ AdminsDom D out := by
  cases step <;> simp only [admins, admin, admin_value, constI32, adminsDom_cons, adminsDom_nil,
    adminDom_value, adminDom_plain, adminDom_ref, adminDom_trap, and_self]

theorem memory_code {ρ : Nat → Nat} {D : Nat → Prop} {s s' : Store H} {f f' : Frame}
    {code out : List Admin} (step : MemoryStep P ⟨s, f, code⟩ ⟨s', f', out⟩) :
    admins ρ code = code ∧ admins ρ out = out ∧ AdminsDom D out := by
  cases step <;> simp only [admins, admin, admin_value, constI32, load8u, store8, adminsDom_cons,
    adminsDom_nil, adminDom_value, adminDom_plain, adminDom_trap, and_self]

end Silmaril.Proofs.Wasm.Game.SpecGlobals
