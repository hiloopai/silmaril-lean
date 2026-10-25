module

public import Silmaril.Wasm.Binaryen.InlDeadFuncRel

@[expose] public section

/-! # Appending a dead function: the reduction families

Every rule of the families `MemoryStep`, `TableStep`, `VariableStep`, `RefStep` and
`AggregateStep` applies as well with the function list of the store replaced and the
instance of the frame extended: they do not look at function code, and they read the
function addresses of the instance only through `ref.func`, whose index exists. The
negative reference tests need the reference to name an existing function (`RefsIn`).
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS

variable {H : Type}

section families

variable {P : Numerics.Profile} {s s' : Store H} {f f' : Frame} {is is' : List Admin}
  {X : List (FuncInst H)}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem memoryStep_ext (h : MemoryStep P ⟨s, f, is⟩ ⟨s', f', is'⟩) (X : List (FuncInst H))
    (l : List Nat) : s'.funcs = s.funcs ∧ f' = f ∧
      MemoryStep P ⟨withFuncs s X, fext f l, is⟩ ⟨withFuncs s' X, fext f l, is'⟩ := by
  cases h <;> refine ⟨rfl, rfl, ?_⟩
  all_goals first
    | (apply MemoryStep.loadIntOob <;> assumption)
    | (apply MemoryStep.loadIntVal <;> assumption)
    | (apply MemoryStep.loadPackOob <;> assumption)
    | (apply MemoryStep.loadPackVal <;> assumption)
    | (apply MemoryStep.loadFloatOob <;> assumption)
    | (apply MemoryStep.loadFloatVal <;> assumption)
    | (apply MemoryStep.vecLoadOob <;> assumption)
    | (apply MemoryStep.vecLoadVal <;> assumption)
    | (apply MemoryStep.vecLoadLaneOob <;> assumption)
    | (apply MemoryStep.vecLoadLaneVal <;> assumption)
    | (apply MemoryStep.storeIntOob <;> assumption)
    | (apply MemoryStep.storeIntVal <;> assumption)
    | (apply MemoryStep.storePackOob <;> assumption)
    | (apply MemoryStep.storePackVal <;> assumption)
    | (apply MemoryStep.storeFloatOob <;> assumption)
    | (apply MemoryStep.storeFloatVal <;> assumption)
    | (apply MemoryStep.vecStoreOob <;> assumption)
    | (apply MemoryStep.vecStoreVal <;> assumption)
    | (apply MemoryStep.vecStoreLaneOob <;> assumption)
    | (apply MemoryStep.vecStoreLaneVal <;> assumption)
    | (apply MemoryStep.size <;> assumption)
    | (apply MemoryStep.growSucceed <;> assumption)
    | (apply MemoryStep.growFail <;> assumption)
    | (apply MemoryStep.fillOob <;> assumption)
    | (apply MemoryStep.fillZero <;> assumption)
    | (apply MemoryStep.fillSucc <;> assumption)
    | (apply MemoryStep.copyOob <;> assumption)
    | (apply MemoryStep.copyZero <;> assumption)
    | (apply MemoryStep.copyLe <;> assumption)
    | (apply MemoryStep.copyGt <;> assumption)
    | (apply MemoryStep.initOob <;> assumption)
    | (apply MemoryStep.initZero <;> assumption)
    | (apply MemoryStep.initSucc <;> assumption)
    | (apply MemoryStep.dataDrop <;> assumption)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem tableStep_ext (h : TableStep P ⟨s, f, is⟩ ⟨s', f', is'⟩) (X : List (FuncInst H))
    (l : List Nat) : s'.funcs = s.funcs ∧ f' = f ∧
      TableStep P ⟨withFuncs s X, fext f l, is⟩ ⟨withFuncs s' X, fext f l, is'⟩ := by
  cases h <;> refine ⟨rfl, rfl, ?_⟩
  all_goals first
    | (apply TableStep.getOob <;> assumption)
    | (apply TableStep.getVal <;> assumption)
    | (apply TableStep.setOob <;> assumption)
    | (apply TableStep.setVal <;> assumption)
    | (apply TableStep.size <;> assumption)
    | (apply TableStep.growSucceed <;> assumption)
    | (apply TableStep.growFail <;> assumption)
    | (apply TableStep.fillOob <;> assumption)
    | (apply TableStep.fillZero <;> assumption)
    | (apply TableStep.fillSucc <;> assumption)
    | (apply TableStep.copyOob <;> assumption)
    | (apply TableStep.copyZero <;> assumption)
    | (apply TableStep.copyLe <;> assumption)
    | (apply TableStep.copyGt <;> assumption)
    | (apply TableStep.initOob <;> assumption)
    | (apply TableStep.initZero <;> assumption)
    | (apply TableStep.initSucc <;> assumption)
    | (apply TableStep.elemDrop <;> assumption)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem aggregateStep_ext (h : AggregateStep ⟨s, f, is⟩ ⟨s', f', is'⟩) (X : List (FuncInst H))
    (l : List Nat) : s'.funcs = s.funcs ∧ f' = f ∧
      AggregateStep ⟨withFuncs s X, fext f l, is⟩ ⟨withFuncs s' X, fext f l, is'⟩ := by
  cases h <;> refine ⟨rfl, rfl, ?_⟩
  all_goals first
    | (apply AggregateStep.structNew <;> assumption)
    | (apply AggregateStep.structNewDefault <;> assumption)
    | (apply AggregateStep.structGetNull <;> assumption)
    | (apply AggregateStep.structGetStruct <;> assumption)
    | (apply AggregateStep.structSetNull <;> assumption)
    | (apply AggregateStep.structSetStruct <;> assumption)
    | (apply AggregateStep.arrayNew <;> assumption)
    | (apply AggregateStep.arrayNewDefault <;> assumption)
    | (apply AggregateStep.arrayNewFixed <;> assumption)
    | (apply AggregateStep.arrayNewElemOob <;> assumption)
    | (apply AggregateStep.arrayNewElemAlloc <;> assumption)
    | (apply AggregateStep.arrayNewDataOob <;> assumption)
    | (apply AggregateStep.arrayNewDataNum <;> assumption)
    | (apply AggregateStep.arrayGetNull <;> assumption)
    | (apply AggregateStep.arrayGetOob <;> assumption)
    | (apply AggregateStep.arrayGetArray <;> assumption)
    | (apply AggregateStep.arraySetNull <;> assumption)
    | (apply AggregateStep.arraySetOob <;> assumption)
    | (apply AggregateStep.arraySetArray <;> assumption)
    | (apply AggregateStep.arrayLenNull <;> assumption)
    | (apply AggregateStep.arrayLenArray <;> assumption)
    | (apply AggregateStep.arrayFillNull <;> assumption)
    | (apply AggregateStep.arrayFillOob <;> assumption)
    | (apply AggregateStep.arrayFillZero <;> assumption)
    | (apply AggregateStep.arrayFillSucc <;> assumption)
    | (apply AggregateStep.arrayCopyNull₁ <;> assumption)
    | (apply AggregateStep.arrayCopyNull₂ <;> assumption)
    | (apply AggregateStep.arrayCopyOob₁ <;> assumption)
    | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
    | (apply AggregateStep.arrayCopyZero <;> assumption)
    | (apply AggregateStep.arrayCopyLe <;> assumption)
    | (apply AggregateStep.arrayCopyGt <;> assumption)
    | (apply AggregateStep.arrayInitElemNull <;> assumption)
    | (apply AggregateStep.arrayInitElemOob₁ <;> assumption)
    | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
    | (apply AggregateStep.arrayInitElemZero <;> assumption)
    | (apply AggregateStep.arrayInitElemSucc <;> assumption)
    | (apply AggregateStep.arrayInitDataNull <;> assumption)
    | (apply AggregateStep.arrayInitDataOob₁ <;> assumption)
    | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)
    | (apply AggregateStep.arrayInitDataZero <;> assumption)
    | (apply AggregateStep.arrayInitDataNum <;> assumption)

theorem variableStep_ext (h : VariableStep ⟨s, f, is⟩ ⟨s', f', is'⟩) (X : List (FuncInst H))
    (l : List Nat) : s'.funcs = s.funcs ∧ f'.module = f.module ∧
      VariableStep ⟨withFuncs s X, fext f l, is⟩ ⟨withFuncs s' X, fext f' l, is'⟩ := by
  cases h with
  | localGet h => exact ⟨rfl, rfl, .localGet h⟩
  | localSet h => exact ⟨rfl, rfl, .localSet h⟩
  | localTee => exact ⟨rfl, rfl, .localTee⟩
  | globalGet h => exact ⟨rfl, rfl, .globalGet h⟩
  | globalSet h => exact ⟨rfl, rfl, .globalSet h⟩

theorem refStep_ext (h : RefStep ⟨s, f, is⟩ ⟨s', f', is'⟩) (hX : FL s.funcs X)
    (hin : RefsIn s.funcs.length is) (l : List Nat) :
    s' = s ∧ f' = f ∧ RefStep ⟨withFuncs s X, fext f l, is⟩ ⟨withFuncs s X, fext f l, is'⟩ := by
  cases h with
  | refNull ht => exact ⟨rfl, rfl, .refNull ht⟩
  | refFunc h => exact ⟨rfl, rfl, .refFunc (mext_funcs_get h)⟩
  | refI31 i => exact ⟨rfl, rfl, .refI31 i⟩
  | isNullTrue => exact ⟨rfl, rfl, .isNullTrue⟩
  | isNullFalse h => exact ⟨rfl, rfl, .isNullFalse h⟩
  | asNonNullNull => exact ⟨rfl, rfl, .asNonNullNull⟩
  | asNonNullAddr h => exact ⟨rfl, rfl, .asNonNullAddr h⟩
  | eqNull => exact ⟨rfl, rfl, .eqNull⟩
  | eqTrue h => exact ⟨rfl, rfl, .eqTrue h⟩
  | eqFalse h => exact ⟨rfl, rfl, .eqFalse h⟩
  | testTrue h => exact ⟨rfl, rfl, .testTrue (refOk_fl hX h)⟩
  | testFalse h =>
    exact ⟨rfl, rfl, .testFalse fun h' =>
      h ((refOk_fl_iff hX (hin.ref (by simp))).1 h')⟩
  | castSucceed h => exact ⟨rfl, rfl, .castSucceed (refOk_fl hX h)⟩
  | castFail h =>
    exact ⟨rfl, rfl, .castFail fun h' =>
      h ((refOk_fl_iff hX (hin.ref (by simp))).1 h')⟩
  | i31GetNull sx => exact ⟨rfl, rfl, .i31GetNull sx⟩
  | i31GetNum sx i => exact ⟨rfl, rfl, .i31GetNum sx i⟩
  | externConvertNull => exact ⟨rfl, rfl, .externConvertNull⟩
  | externConvertAddr h => exact ⟨rfl, rfl, .externConvertAddr h⟩
  | anyConvertNull => exact ⟨rfl, rfl, .anyConvertNull⟩
  | anyConvertAddr r => exact ⟨rfl, rfl, .anyConvertAddr r⟩

end families

end Silmaril.Wasm.Binaryen.InlDF
