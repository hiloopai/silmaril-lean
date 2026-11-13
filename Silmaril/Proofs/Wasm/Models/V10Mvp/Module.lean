module

public import Silmaril.Proofs.Wasm.Models.V10Mvp.Const

/-!
# The Core image of a valid 1.0 module is a module of `v10` up to MVP initialisers

The module-level counterpart of `Lime1Mvp.v10_expr_inFeat`. Component by component:

* types: a valid 1.0 function type has at most one result, so no multi-value;
* imports, memories, globals: MVP types; mutable globals are in `v10`;
* globals, element and data offsets: single constant instructions (`constExprB_v10`);
* tables and element initialisers: the canonical MVP initialisers, erased by `mvpNorm`;
* functions: `Lime1Mvp.v10_expr_inFeat`; data segments use memory 0 (`data_mem_zero`);
* one memory and one table: `ModuleValid.singleMemory`, `singleTable` (`count_mem`,
  `count_tab`).

**`v10_inFeatM`**: `ModuleValid m → InFeatM v10 m.toCore`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Mvp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Mvp

@[simp] theorem v10_has_intNum : v10.has .intNum = true := by decide
@[simp] theorem v10_has_memory : v10.has .memory = true := by decide
@[simp] theorem v10_has_table : v10.has .table = true := by decide
@[simp] theorem v10_has_globals : v10.has .globals = true := by decide
@[simp] theorem v10_has_mutGlobal : v10.has .mutGlobal = true := by decide

theorem count_mem (m : Silmaril.Wasm.V1.Module) :
    ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isMemory).length +
      m.memories.length = (Silmaril.Wasm.V1.Validation.moduleContext m).memories.length := by
  simp only [Silmaril.Wasm.V1.Validation.moduleContext, List.length_append,
    Nat.add_right_cancel_iff]
  generalize m.imports = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    rcases i with ⟨_, _, d⟩
    cases d <;> simp [Silmaril.Wasm.V1.Import.toCore, Silmaril.Wasm.V1.ImportDesc.toCore,
      Import.isMemory, List.filter_cons, ih]

theorem count_tab (m : Silmaril.Wasm.V1.Module) :
    ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isTable).length +
      m.tables.length = (Silmaril.Wasm.V1.Validation.moduleContext m).tables.length := by
  simp only [Silmaril.Wasm.V1.Validation.moduleContext, List.length_append,
    Nat.add_right_cancel_iff]
  generalize m.imports = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    rcases i with ⟨_, _, d⟩
    cases d <;> simp [Silmaril.Wasm.V1.Import.toCore, Silmaril.Wasm.V1.ImportDesc.toCore,
      Import.isTable, List.filter_cons, ih]

theorem valType_v10 (t : Silmaril.Wasm.V1.ValType) :
    ValType.inFeatB v10 (Silmaril.Wasm.V1.ValType.toCore t) = true := by
  cases t <;> rfl

theorem recType_v10 {t : Silmaril.Wasm.V1.FuncType}
    (h : Silmaril.Wasm.V1.Validation.FuncTypeValid t) :
    RecType.inFeatB v10 t.toCoreRec = true := by
  have h' : t.results.length ≤ 1 := h
  simp [RecType.inFeatB, SubType.inFeatB, FuncType.inFeatB, Silmaril.Wasm.V1.FuncType.toCoreRec,
    Silmaril.Wasm.V1.FuncType.toCore, valType_v10, h']

theorem tableType_v10 (t : Silmaril.Wasm.V1.TableType) :
    TableType.inFeatB v10 t.toCore = true := by
  simp [TableType.inFeatB, Silmaril.Wasm.V1.TableType.toCore, Silmaril.Wasm.V1.funcref]

theorem globalType_v10 (t : Silmaril.Wasm.V1.GlobalType) :
    GlobalType.inFeatB v10 t.toCore = true := by
  simp [GlobalType.inFeatB, Silmaril.Wasm.V1.GlobalType.toCore, valType_v10]

theorem memory_v10 (t : Silmaril.Wasm.V1.MemoryType) :
    MemoryType.inFeatB v10 t.toCore = true := by
  simp [MemoryType.inFeatB, Silmaril.Wasm.V1.MemoryType.toCore]

theorem import_v10 (i : Silmaril.Wasm.V1.Import) :
    ExternType.inFeatB v10 i.toCore.type = true := by
  rcases i with ⟨_, _, d⟩
  cases d <;> simp [ExternType.inFeatB, Silmaril.Wasm.V1.Import.toCore,
    Silmaril.Wasm.V1.ImportDesc.toCore, tableType_v10, globalType_v10, memory_v10]

theorem global_v10 {C : Silmaril.Wasm.V1.Validation.Context} {g : Silmaril.Wasm.V1.Global}
    (h : Silmaril.Wasm.V1.Validation.GlobalValid C g) :
    Global.inFeatB v10 g.toCore = true := by
  simp [Global.inFeatB, Silmaril.Wasm.V1.Global.toCore, globalType_v10, constExprB_v10 h]

theorem table_v10 (t : Silmaril.Wasm.V1.TableType) :
    Table.inFeatB v10 { t.toCoreTable with init := normInit t.toCoreTable.init } = true := by
  simp [Table.inFeatB, Silmaril.Wasm.V1.TableType.toCoreTable, tableType_v10, normInit,
    isMvpInit]

theorem func_v10 (f : Silmaril.Wasm.V1.Func) : Func.inFeatB v10 f.toCore = true := by
  simp [Func.inFeatB, Silmaril.Wasm.V1.Func.toCore, valType_v10, v10_expr_inFeat]

theorem elem_v10 {C : Silmaril.Wasm.V1.Validation.Context} {e : Silmaril.Wasm.V1.Elem}
    (h : Silmaril.Wasm.V1.Validation.ElemValid C e) :
    Elem.inFeatB v10 { e.toCore with init := e.toCore.init.map normInit } = true := by
  simp [Elem.inFeatB, Silmaril.Wasm.V1.Elem.toCore, Silmaril.Wasm.V1.funcref, normInit,
    isMvpInit, ElemMode.inFeatB, constExprB_v10 h.offset]

/-- A data segment of a valid 1.0 module uses memory 0. -/
theorem data_mem_zero {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) {d : Silmaril.Wasm.V1.Data}
    (hd : d ∈ m.data) : d.memory.toNat = 0 := by
  obtain ⟨mt, hmt⟩ := (hv.data d hd).memory
  have hlt := (List.getElem?_eq_some_iff.mp hmt).1
  have h1 := hv.singleMemory
  omega

theorem data_v10 {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) {d : Silmaril.Wasm.V1.Data}
    (hd : d ∈ m.data) : Data.inFeatB v10 d.toCore = true := by
  simp [Data.inFeatB, Silmaril.Wasm.V1.Data.toCore, DataMode.inFeatB, memIdxB,
    data_mem_zero hv hd, constExprB_v10 (hv.data d hd).offset]

@[simp] theorem v10_has_exn : v10.has .exn = false := by decide
@[simp] theorem v10_has_multiMemory : v10.has .multiMemory = false := by decide

/-- **The Core image of a valid 1.0 module is a module of `v10` up to the canonical MVP
initialisers.** -/
theorem v10_inFeatM {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) :
    InFeatM v10 (Silmaril.Wasm.V1.Module.toCore m) := by
  have hmem : ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isMemory).length +
      m.memories.length ≤ 1 := by
    rw [count_mem]
    exact hv.singleMemory
  have htab : ((m.imports.map Silmaril.Wasm.V1.Import.toCore).filter Import.isTable).length +
      m.tables.length ≤ 1 := by
    rw [count_tab]
    exact hv.singleTable
  show Module.inFeatB v10 (mvpNorm (Silmaril.Wasm.V1.Module.toCore m)) = true
  rw [Silmaril.Proofs.Wasm.Models.Lime1Mvp.inFeatB_mvpNorm]
  simp only [Silmaril.Wasm.V1.Module.toCore, List.length_map, Bool.and_eq_true, List.all_map,
    List.all_eq_true, Function.comp_apply, Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_nil,
    true_or, and_true, v10_has_multiMemory]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨fun t ht => recType_v10 (hv.types t ht), fun i _ => import_v10 i⟩,
    fun g hg => global_v10 (hv.globals g hg)⟩, fun t _ => memory_v10 t⟩, fun t _ => table_v10 t⟩,
    fun f _ => func_v10 f⟩, fun e he => elem_v10 (hv.elements e he)⟩,
    fun d hd => data_v10 hv hd⟩,
    by omega⟩, Or.inl (by omega)⟩

end Silmaril.Proofs.Wasm.Models.V10Mvp
