module

public import Silmaril.Wasm.Lime1.Execution.Step
public import Silmaril.Wasm.V1.Execution.Step
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Wasm.Execution.Runtime.Map

/-! # Runtime transport from Wasm1 to Lime1

The common runtime carriers retain values, addresses and local frames. Source
code in function stores, administrative instructions and label continuations is
mapped structurally. Host relations are related explicitly, including returns
with changed stores and divergence outcomes.
-/

@[expose] public section
namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

abbrev codeToLime (code : List Admin) : List Lime1.Execution.Admin :=
  AdminInstr.mapList Instr.toLime code

@[simp] theorem codeToLime_nil : codeToLime [] = [] := rfl

@[simp] theorem codeToLime_cons (i : Admin) (is : List Admin) :
    codeToLime (i :: is) = AdminInstr.map Instr.toLime i :: codeToLime is := rfl

@[simp] theorem codeToLime_append (xs ys : List Admin) :
    codeToLime (xs ++ ys) = codeToLime xs ++ codeToLime ys := AdminInstr.mapList_append _ _ _

def Config.toLime {H : Type*} (c : Config H) : Lime1.Execution.Config H :=
  ⟨c.store.mapCode Func.toLime, c.frame, codeToLime c.code⟩

@[simp] theorem map_value (v : Value) :
    AdminInstr.map Instr.toLime (value v) = Lime1.Execution.value v := by
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

@[simp] theorem map_values (vs : List Value) :
    codeToLime (values vs) = Lime1.Execution.values vs := by
  simp [codeToLime, values, Lime1.Execution.values, List.map_map, Function.comp_def]

@[simp] theorem map_expression (es : Expr) :
    codeToLime (expression es) = Lime1.Execution.expression (Expr.toLime es) := by
  simp [codeToLime, expression, Lime1.Execution.expression, Expr.toLime_eq_map,
    List.map_map, Function.comp_def, AdminInstr.map]

@[simp] theorem map_result (r : Result) :
    codeToLime (result r) = Lime1.Execution.result r := by
  cases r with
  | values vs => exact map_values vs
  | trap => rfl

@[simp] theorem map_frameMemory {H : Type*} (s : Store H) (f : Frame) :
    Lime1.Execution.frameMemory (s.mapCode Func.toLime) f = frameMemory s f := rfl

@[simp] theorem map_frameTable {H : Type*} (s : Store H) (f : Frame) :
    Lime1.Execution.frameTable (s.mapCode Func.toLime) f = frameTable s f := rfl

@[simp] theorem map_setMemory {H : Type*} (s : Store H) (a : MemAddr) (m : MemInst) :
    (setMemory s a m).mapCode Func.toLime =
      Lime1.Execution.setMemory (s.mapCode Func.toLime) a m := rfl

@[simp] theorem map_setGlobal {H : Type*} (s : Store H) (a : GlobalAddr) (g : GlobalInst) :
    (setGlobal s a g).mapCode Func.toLime =
      Lime1.Execution.setGlobal (s.mapCode Func.toLime) a g := rfl

@[simp] theorem blockType_toLime (types : List FuncType) (bt : BlockType) :
    Lime1.Execution.blockType? types bt.toLime = some ⟨[], bt.toList⟩ := by
  cases bt <;> rfl

@[simp] theorem map_values_list (vs : List Value) :
    (values vs).map (AdminInstr.map Instr.toLime) = Lime1.Execution.values vs := by
  simpa only [codeToLime, AdminInstr.mapList_eq_map] using map_values vs

@[simp] theorem map_expression_list (es : Expr) :
    (expression es).map (AdminInstr.map Instr.toLime) =
      Lime1.Execution.expression (Expr.toLime es) := by
  simpa only [codeToLime, AdminInstr.mapList_eq_map] using map_expression es

@[simp] theorem lowerLabel_toLime (i : LabelIdx) : Lime1.Execution.lowerLabel i = lowerLabel i := rfl

@[simp] theorem map_result_list (r : Result) :
    (result r).map (AdminInstr.map Instr.toLime) = Lime1.Execution.result r := by
  simpa only [codeToLime, AdminInstr.mapList_eq_map] using map_result r

end Silmaril.Wasm.V1.Execution
