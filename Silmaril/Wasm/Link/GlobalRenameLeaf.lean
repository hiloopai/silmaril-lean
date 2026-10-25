module

public import Silmaril.Wasm.Link.GlobalPermutation

/-! # Stateful leaf reductions under global address renaming

Global renaming changes module global addresses and global exports; GC objects,
tables, memories and segments keep their addresses, closed tags and contents.
Every aggregate, table and memory leaf rule therefore transports the same code
and runtime output, while exact allocations and updates preserve the renamed
store relation. Bulk-operation expansions include both copy directions.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.GlobalPermutation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

private theorem type_lookup {p : Nat ≃ Nat} {f : Frame}
    {x : TypeIdx} {d : DefType} (h : f.type? x = some d) :
    (frame p f).type? x = some d := by
  simpa only [Frame.type?, frame, moduleView] using h

private theorem table_lookup {p : Nat ≃ Nat} {source target : Store H} {f : Frame}
    (stores : Renamed p source target)
    {x : TableIdx} {a : Nat} {ti : TableInst} (h : source.table? f x = some (a, ti)) :
    target.table? (frame p f) x = some (a, ti) := by
  simpa only [Store.table?, frame, moduleView, ← stores.tables] using h

private theorem elem_lookup {p : Nat ≃ Nat} {source target : Store H} {f : Frame}
    (stores : Renamed p source target)
    {x : ElemIdx} {a : Nat} {ei : ElemInst} (h : source.elem? f x = some (a, ei)) :
    target.elem? (frame p f) x = some (a, ei) := by
  simpa only [Store.elem?, frame, moduleView, ← stores.elems] using h

private theorem mem_lookup {p : Nat ≃ Nat} {source target : Store H} {f : Frame}
    (stores : Renamed p source target)
    {x : MemIdx} {a : Nat} {mi : MemInst} (h : source.mem? f x = some (a, mi)) :
    target.mem? (frame p f) x = some (a, mi) := by
  simpa only [Store.mem?, frame, moduleView, ← stores.mems] using h

private theorem data_lookup {p : Nat ≃ Nat} {source target : Store H} {f : Frame}
    (stores : Renamed p source target)
    {x : DataIdx} {a : Nat} {di : DataInst} (h : source.data? f x = some (a, di)) :
    target.data? (frame p f) x = some (a, di) := by
  simpa only [Store.data?, frame, moduleView, ← stores.datas] using h

/-- All aggregate rules transport their exact GC allocations, updates and
bulk-operation expansions through global address renaming. -/
theorem aggregate_step {p : Nat ≃ Nat} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (stores : Renamed p source target)
    (step : AggregateStep ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', AggregateStep ⟨target, frame p f, code⟩ ⟨target', frame p f', out⟩ ∧
      Renamed p source' target' := by
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
theorem table_step {p : Nat ≃ Nat} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (stores : Renamed p source target)
    (h : TableStep P ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', TableStep P ⟨target, frame p f, code⟩ ⟨target', frame p f', out⟩ ∧
      Renamed p source' target' := by
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
theorem memory_step {p : Nat ≃ Nat} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (stores : Renamed p source target)
    (h : MemoryStep P ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', MemoryStep P ⟨target, frame p f, code⟩ ⟨target', frame p f', out⟩ ∧
      Renamed p source' target' := by
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


end Silmaril.Wasm.Link.GC.GlobalPermutation
