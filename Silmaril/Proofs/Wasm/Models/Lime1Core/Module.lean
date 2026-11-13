module

public import Silmaril.Proofs.Wasm.Models.Lime1Core.InFeat

/-!
# The Core image of a Lime1 module is a module of `v30`, and not of `lime1` once it has a table

* `module_inFeat_v30`: the Core image of every Lime1 module is in `v30` (no validity needed:
  `v30` has multi-memory and reference types, so the counting conditions hold);
* `validIn_v30`: the Core image of a valid Lime1 module is `ValidIn v30` (with the copied
  `Lime1.Validation.ModuleValid.toCore`);
* `not_inFeat_lime1_of_table`, `not_inFeat_lime1_of_elem`: **the Core image of a Lime1 module
  with a table (an element segment) is not in `lime1`**. Core spells the implicit MVP table
  initialiser as `ref.null func` and a function-index element as `ref.func f`, and the
  restricted syntax (`Silmaril.Wasm.Models.Syntax`) asks for `refTypes` for both, a capability
  `lime1` (like `v10`) does not have. So `core|lime1` as a restriction of Core syntax misses the
  canonical images of MVP tables; the embedding below targets `core|v30`, and its runtime part
  stays inside `lime1` (`storeIn_image`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Core

open Silmaril.Wasm Silmaril.Wasm.Models

@[simp] theorem v30_intNum : v30.has .intNum = true := by decide
@[simp] theorem v30_floatNum : v30.has .floatNum = true := by decide
@[simp] theorem v30_memory : v30.has .memory = true := by decide
@[simp] theorem v30_table : v30.has .table = true := by decide
@[simp] theorem v30_globals : v30.has .globals = true := by decide
@[simp] theorem v30_mutGlobal : v30.has .mutGlobal = true := by decide
@[simp] theorem v30_multiValue : v30.has .multiValue = true := by decide
@[simp] theorem v30_extConst : v30.has .extConst = true := by decide
@[simp] theorem v30_refTypes : v30.has .refTypes = true := by decide
@[simp] theorem v30_multiMemory : v30.has .multiMemory = true := by decide

theorem expr_v30 (e : List Silmaril.Wasm.Lime1.Instr) :
    Instr.insInFeatB v30 (Silmaril.Wasm.Lime1.Expr.toCore e) = true :=
  insInFeatB_mono lime1_le_v30 _ (expr_inFeat e)

theorem constExpr_v30 (e : List Silmaril.Wasm.Lime1.Instr) :
    constExprB v30 (Silmaril.Wasm.Lime1.Expr.toCore e) = true := by
  simp [constExprB, expr_v30]

theorem valType_v30 (t : Silmaril.Wasm.V1.ValType) :
    ValType.inFeatB v30 (Silmaril.Wasm.V1.ValType.toCore t) = true := by
  cases t <;> rfl

theorem recType_v30 (t : Silmaril.Wasm.V1.FuncType) :
    RecType.inFeatB v30 t.toCoreRec = true := by
  simp [RecType.inFeatB, SubType.inFeatB, FuncType.inFeatB, Silmaril.Wasm.V1.FuncType.toCoreRec,
    Silmaril.Wasm.V1.FuncType.toCore, valType_v30]

theorem tableType_v30 (t : Silmaril.Wasm.V1.TableType) :
    TableType.inFeatB v30 t.toCore = true := by
  simp [TableType.inFeatB, Silmaril.Wasm.V1.TableType.toCore, Silmaril.Wasm.V1.funcref]

theorem globalType_v30 (t : Silmaril.Wasm.V1.GlobalType) :
    GlobalType.inFeatB v30 t.toCore = true := by
  simp [GlobalType.inFeatB, Silmaril.Wasm.V1.GlobalType.toCore, valType_v30]

theorem import_v30 (i : Silmaril.Wasm.V1.Import) :
    ExternType.inFeatB v30 i.toCore.type = true := by
  rcases i with ⟨_, _, d⟩
  cases d <;> simp [ExternType.inFeatB, Silmaril.Wasm.V1.Import.toCore,
    Silmaril.Wasm.V1.ImportDesc.toCore, tableType_v30, globalType_v30, MemoryType.inFeatB,
    Silmaril.Wasm.V1.MemoryType.toCore]

theorem inFeatB_refNull (S : FeatureSet) (h : HeapType) :
    Instr.inFeatB S (.refNull h) = (S.has .refTypes && HeapType.inFeatB S h) := rfl

theorem inFeatB_refFunc (S : FeatureSet) (f : FuncIdx) :
    Instr.inFeatB S (.refFunc f) = S.has .refTypes := rfl

theorem constExprB_single (S : FeatureSet) (i : Instr) (h : simpleConst [i] = true) :
    constExprB S [i] = Instr.inFeatB S i := by
  simp [constExprB, Instr.insInFeatB, h]

theorem refNull_v30 : constExprB v30 [.refNull (.abstract .func)] = true := by
  rw [constExprB_single _ _ rfl, inFeatB_refNull]
  rfl

theorem refFunc_v30 (f : FuncIdx) : constExprB v30 (Silmaril.Wasm.Lime1.funcRef f) = true := by
  rw [Silmaril.Wasm.Lime1.funcRef, constExprB_single _ _ rfl, inFeatB_refFunc]
  rfl

/-- **The Core image of a Lime1 module is in `v30`.** -/
theorem module_inFeat_v30 (m : Silmaril.Wasm.Lime1.Module) :
    Module.InFeat v30 (Silmaril.Wasm.Lime1.Module.toCore m) := by
  simp [Module.InFeat, Module.inFeatB, Silmaril.Wasm.Lime1.Module.toCore, List.all_map,
    Function.comp_def, recType_v30, import_v30, Global.inFeatB, globalType_v30, constExpr_v30,
    MemoryType.inFeatB, Silmaril.Wasm.V1.MemoryType.toCore, Table.inFeatB,
    Silmaril.Wasm.Lime1.tableToCore, tableType_v30, refNull_v30, Func.inFeatB,
    Silmaril.Wasm.Lime1.Func.toCore, valType_v30, expr_v30, Elem.inFeatB,
    Silmaril.Wasm.Lime1.Elem.toCore, refFunc_v30, ElemMode.inFeatB, Data.inFeatB,
    Silmaril.Wasm.Lime1.Data.toCore, DataMode.inFeatB, memIdxB, Silmaril.Wasm.Lime1.Global.toCore,
    Silmaril.Wasm.V1.funcref]

/-- **The Core image of a valid Lime1 module is a valid module of `v30`.** -/
theorem validIn_v30 {m : Silmaril.Wasm.Lime1.Module}
    (h : Silmaril.Wasm.Lime1.Validation.ModuleValid m) :
    ValidIn v30 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  ⟨Silmaril.Wasm.Lime1.Validation.ModuleValid.toCore h, module_inFeat_v30 m⟩

/-- The implicit MVP table initialiser is not a constant expression of `lime1`. -/
theorem refNull_not_lime1 : constExprB lime1 [.refNull (.abstract .func)] = false := by
  rw [constExprB_single _ _ rfl, inFeatB_refNull]
  rfl

/-- **The Core image of a Lime1 module with a table is not in `lime1`.** -/
theorem not_inFeat_lime1_of_table {m : Silmaril.Wasm.Lime1.Module} (h : m.tables ≠ []) :
    ¬ Module.InFeat lime1 (Silmaril.Wasm.Lime1.Module.toCore m) := by
  obtain ⟨t, ts, e⟩ := List.exists_cons_of_ne_nil h
  intro hm
  have ht : Table.inFeatB lime1 (Silmaril.Wasm.Lime1.tableToCore t) = true := by
    simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true, List.all_eq_true] at hm
    exact hm.1.1.1.1.1.2 _ (by simp [Silmaril.Wasm.Lime1.Module.toCore, e])
  simp [Table.inFeatB, Silmaril.Wasm.Lime1.tableToCore, refNull_not_lime1] at ht

/-- **The Core image of a Lime1 module with an element segment that names a function is not in
`lime1`.** -/
theorem not_inFeat_lime1_of_elem {m : Silmaril.Wasm.Lime1.Module} {e : Silmaril.Wasm.Lime1.Elem}
    (he : e ∈ m.elems) (hi : e.init ≠ []) :
    ¬ Module.InFeat lime1 (Silmaril.Wasm.Lime1.Module.toCore m) := by
  obtain ⟨f, fs, e'⟩ := List.exists_cons_of_ne_nil hi
  intro hm
  have hE : Elem.inFeatB lime1 (Silmaril.Wasm.Lime1.Elem.toCore e) = true := by
    simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true, List.all_eq_true] at hm
    exact hm.1.1.1.2 _ (by simp [Silmaril.Wasm.Lime1.Module.toCore]; exact ⟨e, he, rfl⟩)
  have : constExprB lime1 (Silmaril.Wasm.Lime1.funcRef f) = false := by
    rw [Silmaril.Wasm.Lime1.funcRef, constExprB_single _ _ rfl, inFeatB_refFunc]
    rfl
  simp [Elem.inFeatB, Silmaril.Wasm.Lime1.Elem.toCore, e', this] at hE

end Silmaril.Proofs.Wasm.Models.Lime1Core
