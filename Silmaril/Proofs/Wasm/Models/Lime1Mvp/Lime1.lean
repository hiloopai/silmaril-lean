module

public import Silmaril.Proofs.Wasm.Models.Lime1Mvp.Syntax
public import Silmaril.Wasm.Models.Lime1Core.Thms

/-!
# The Core image of a valid Lime1 module is a module of `lime1` up to MVP initialisers

* `count_mem`, `count_tab`: the Core image keeps the number of imported memories and tables;
* `data_mem_zero`: a valid Lime1 data segment uses memory 0;
* **`lime1_inFeatM`**: the Core image of a valid Lime1 module is `InFeatM lime1`. This is the
  positive counterpart of `Lime1Core.not_inFeat_lime1_of_table`: the only obstruction to
  `InFeat lime1` is the two canonical MVP initialisers.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Mvp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Mvp
open Silmaril.Proofs.Wasm.Models.Lime1Core

theorem count_mem (m : Silmaril.Wasm.Lime1.Module) :
    ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isMemory).length +
      m.memories.length = (Silmaril.Wasm.Lime1.Validation.moduleContext m).memories.length := by
  simp only [Silmaril.Wasm.Lime1.Validation.moduleContext, List.length_append,
    Nat.add_right_cancel_iff]
  generalize m.imports = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    rcases i with ⟨_, _, d⟩
    cases d <;> simp [Silmaril.Wasm.V1.Import.toCore, Silmaril.Wasm.V1.ImportDesc.toCore,
      Import.isMemory, List.filter_cons, ih]

theorem count_tab (m : Silmaril.Wasm.Lime1.Module) :
    ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isTable).length +
      m.tables.length = (Silmaril.Wasm.Lime1.Validation.moduleContext m).tables.length := by
  simp only [Silmaril.Wasm.Lime1.Validation.moduleContext, List.length_append,
    Nat.add_right_cancel_iff]
  generalize m.imports = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    rcases i with ⟨_, _, d⟩
    cases d <;> simp [Silmaril.Wasm.V1.Import.toCore, Silmaril.Wasm.V1.ImportDesc.toCore,
      Import.isTable, List.filter_cons, ih]

@[simp] theorem lime1_has_exn : lime1.has .exn = false := by decide
@[simp] theorem lime1_has_multiMemory : lime1.has .multiMemory = false := by decide

theorem valType_lime1 (t : Silmaril.Wasm.V1.ValType) :
    ValType.inFeatB lime1 (Silmaril.Wasm.V1.ValType.toCore t) = true := by
  cases t <;> rfl

theorem recType_lime1 (t : Silmaril.Wasm.V1.FuncType) :
    RecType.inFeatB lime1 t.toCoreRec = true := by
  simp [RecType.inFeatB, SubType.inFeatB, FuncType.inFeatB, Silmaril.Wasm.V1.FuncType.toCoreRec,
    Silmaril.Wasm.V1.FuncType.toCore, valType_lime1]

theorem tableType_lime1 (t : Silmaril.Wasm.V1.TableType) :
    TableType.inFeatB lime1 t.toCore = true := by
  simp [TableType.inFeatB, Silmaril.Wasm.V1.TableType.toCore, Silmaril.Wasm.V1.funcref]

theorem globalType_lime1 (t : Silmaril.Wasm.V1.GlobalType) :
    GlobalType.inFeatB lime1 t.toCore = true := by
  simp [GlobalType.inFeatB, Silmaril.Wasm.V1.GlobalType.toCore, valType_lime1]

theorem import_lime1 (i : Silmaril.Wasm.V1.Import) :
    ExternType.inFeatB lime1 i.toCore.type = true := by
  rcases i with ⟨_, _, d⟩
  cases d <;> simp [ExternType.inFeatB, Silmaril.Wasm.V1.Import.toCore,
    Silmaril.Wasm.V1.ImportDesc.toCore, tableType_lime1, globalType_lime1, MemoryType.inFeatB,
    Silmaril.Wasm.V1.MemoryType.toCore]

theorem constExpr_lime1 (e : List Silmaril.Wasm.Lime1.Instr) :
    constExprB lime1 (Silmaril.Wasm.Lime1.Expr.toCore e) = true := by
  simp [constExprB, expr_inFeat]

theorem normInit_funcRef (f : FuncIdx) : normInit (Silmaril.Wasm.Lime1.funcRef f) = [] := rfl

theorem normInit_refNull : normInit [.refNull (.abstract .func)] = [] := rfl

/-- A data segment of a valid Lime1 module uses memory 0. -/
theorem data_mem_zero {m : Silmaril.Wasm.Lime1.Module}
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m) {d : Silmaril.Wasm.Lime1.Data}
    (hd : d ∈ m.data) : d.memory.toNat = 0 := by
  obtain ⟨mt, hmt⟩ := (hv.data d hd).memory
  have hlt := (List.getElem?_eq_some_iff.mp hmt).1
  have h1 := hv.singleMemory
  omega

theorem global_lime1 (g : Silmaril.Wasm.Lime1.Global) :
    Global.inFeatB lime1 g.toCore = true := by
  simp [Global.inFeatB, Silmaril.Wasm.Lime1.Global.toCore, globalType_lime1, constExpr_lime1]

theorem memory_lime1 (t : Silmaril.Wasm.V1.MemoryType) :
    MemoryType.inFeatB lime1 t.toCore = true := by
  simp [MemoryType.inFeatB, Silmaril.Wasm.V1.MemoryType.toCore]

theorem table_lime1 (t : Silmaril.Wasm.V1.TableType) :
    Table.inFeatB lime1 { Silmaril.Wasm.Lime1.tableToCore t with
      init := normInit (Silmaril.Wasm.Lime1.tableToCore t).init } = true := by
  simp [Table.inFeatB, Silmaril.Wasm.Lime1.tableToCore, tableType_lime1, normInit_refNull]

theorem func_lime1 (f : Silmaril.Wasm.Lime1.Func) : Func.inFeatB lime1 f.toCore = true := by
  simp [Func.inFeatB, Silmaril.Wasm.Lime1.Func.toCore, valType_lime1, expr_inFeat]

theorem elem_lime1 (e : Silmaril.Wasm.Lime1.Elem) :
    Elem.inFeatB lime1 { e.toCore with init := e.toCore.init.map normInit } = true := by
  simp [Elem.inFeatB, Silmaril.Wasm.Lime1.Elem.toCore, Silmaril.Wasm.V1.funcref,
    normInit_funcRef, ElemMode.inFeatB, constExpr_lime1]

theorem data_lime1 {d : Silmaril.Wasm.Lime1.Data} (h0 : d.memory.toNat = 0) :
    Data.inFeatB lime1 d.toCore = true := by
  simp [Data.inFeatB, Silmaril.Wasm.Lime1.Data.toCore, DataMode.inFeatB, memIdxB, h0,
    constExpr_lime1]

/-- **The Core image of a valid Lime1 module is a module of `lime1` up to the canonical MVP
initialisers.** -/
theorem lime1_inFeatM {m : Silmaril.Wasm.Lime1.Module}
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m) :
    InFeatM lime1 (Silmaril.Wasm.Lime1.Module.toCore m) := by
  have hmem : ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isMemory).length +
      m.memories.length ≤ 1 := by
    rw [count_mem]
    exact hv.singleMemory
  have htab : ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isTable).length +
      m.tables.length ≤ 1 := by
    rw [count_tab]
    exact hv.singleTable
  show Module.inFeatB lime1 (mvpNorm (Silmaril.Wasm.Lime1.Module.toCore m)) = true
  rw [inFeatB_mvpNorm]
  simp only [Silmaril.Wasm.Lime1.Module.toCore, List.length_map, Bool.and_eq_true, List.all_map,
    List.all_eq_true, Function.comp_apply, Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_nil,
    true_or, and_true, lime1_has_multiMemory]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨fun t _ => recType_lime1 t, fun i _ => import_lime1 i⟩,
    fun g _ => global_lime1 g⟩, fun t _ => memory_lime1 t⟩, fun t _ => table_lime1 t⟩,
    fun f _ => func_lime1 f⟩, fun e _ => elem_lime1 e⟩,
    fun d hd => data_lime1 (data_mem_zero hv hd)⟩,
    by omega⟩, Or.inl (by omega)⟩

end Silmaril.Proofs.Wasm.Models.Lime1Mvp
