module

public import Silmaril.Proofs.Wasm.Models.V2Core.Const

/-!
# The Core image of a valid 2.0 module is a valid module of `v20`

* the syntactic parts: types, imports, memories, tables and functions of the image are in `v20`
  for every 2.0 module;
* the parts that need validation: constant expressions are single instructions
  (`Const.lean`), active data segments use memory `0` (`Datamode_ok/active`,
  `6-typing:632`), and there is at most one memory (`6-typing:698`);
* `module_inFeat`: `Module.InFeat v20` of the image of a valid module; `validIn_image`:
  `ValidIn v20` (with silmaril-lean's `V2.ModuleValid.toCore`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Models

/-- A `Forall₂` relates every element on the left to something. -/
theorem forall₂_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ x ∈ l, ∃ y, R x y
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons hab hrest, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hab⟩
    · exact forall₂_left hrest x hx

/-- `List.mapM` and `List.all`: every image satisfies `P`. -/
theorem mapM_all {α β : Type} {f : α → Option β} {P : β → Bool} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      (∀ x ∈ l, ∀ y, f x = some y → P y = true) → l'.all P = true
  | [], l', h, _ => by
    have e : l' = [] := (Option.some.inj h).symm
    simp [e]
  | x :: l, l', h, hP => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, hx, hl] at h
      | some ys =>
        have e : l' = y :: ys := by simpa [List.mapM_cons, hx, hl] using h.symm
        have hy : P y = true := hP x (by simp) y hx
        have hys : ys.all P = true := mapM_all hl fun z hz => hP z (by simp [hz])
        simp [e, hy, hys]

/-! ## Syntactic parts -/

theorem resultType_v20 (ts : Silmaril.Wasm.V2.ResultType) :
    (Silmaril.Wasm.V2.ResultType.toCore ts).all (ValType.inFeatB v20) = true := by
  simp [Silmaril.Wasm.V2.ResultType.toCore, valType_v20]

theorem recType_v20 (t : Silmaril.Wasm.V2.FuncType) :
    RecType.inFeatB v20 t.toCoreRec = true := by
  simp [RecType.inFeatB, SubType.inFeatB, FuncType.inFeatB, Silmaril.Wasm.V2.FuncType.toCoreRec,
    Silmaril.Wasm.V2.FuncType.toCore, resultType_v20]

theorem refType_v20 (t : Silmaril.Wasm.V2.RefType) : RefType.inFeatB v20 t.toCore = true := by
  cases t <;> simp [RefType.inFeatB, HeapType.inFeatB, AbsHeapType.inFeatB,
    Silmaril.Wasm.V2.RefType.toCore]

theorem tableType_v20 (t : Silmaril.Wasm.V2.TableType) :
    TableType.inFeatB v20 t.toCore = true := by
  simp [TableType.inFeatB, Silmaril.Wasm.V2.TableType.toCore, refType_v20]

theorem globalType_v20 (t : Silmaril.Wasm.V2.GlobalType) :
    GlobalType.inFeatB v20 t.toCore = true := by
  simp [GlobalType.inFeatB, Silmaril.Wasm.V2.GlobalType.toCore, valType_v20]

theorem memoryType_v20 (t : Silmaril.Wasm.V2.MemoryType) :
    MemoryType.inFeatB v20 t.toCore = true := by
  simp [MemoryType.inFeatB, Silmaril.Wasm.V2.MemoryType.toCore]

theorem import_v20 (i : Silmaril.Wasm.V2.Import) :
    ExternType.inFeatB v20 i.toCore.type = true := by
  rcases i with ⟨_, _, d⟩
  cases d <;> simp [ExternType.inFeatB, Silmaril.Wasm.V2.Import.toCore,
    Silmaril.Wasm.V2.ImportDesc.toCore, tableType_v20, globalType_v20, memoryType_v20]

theorem table_v20 (t : Silmaril.Wasm.V2.TableType) :
    Table.inFeatB v20 t.toCoreTable = true := by
  have hc : constExprB v20 [.refNull t.element.toCoreHeap] = true := by
    have hi : Instr.insInFeatB v20 [.refNull t.element.toCoreHeap] = true := by
      simp [Instr.insInFeatB, Instr.inFeatB, Instr.headB, refNull_v20]
    simp only [constExprB, hi, Bool.true_and]
    rfl
  simp [Table.inFeatB, Silmaril.Wasm.V2.TableType.toCoreTable, tableType_v20, hc]

theorem func_v20 {f : Silmaril.Wasm.V2.Func} {cf : Silmaril.Wasm.Func}
    (h : Silmaril.Wasm.V2.Func.toCore f = some cf) : Func.inFeatB v20 cf = true := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [Func.inFeatB, valType_v20, expr_inFeat _ hb]

/-! ## Parts that need validation -/

theorem global_v20 {C : Context} {g : Silmaril.Wasm.V2.Global} {gt : Silmaril.Wasm.V2.GlobalType}
    (hok : GlobalOk C g gt) {cg : Silmaril.Wasm.Global}
    (h : Silmaril.Wasm.V2.Global.toCore g = some cg) : Global.inFeatB v20 cg = true := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [Global.inFeatB, globalType_v20, constExpr_v20 hok.2.2 hb]

theorem elemMode_v20 {C : Context} {md : Silmaril.Wasm.V2.ElemMode}
    {rt : Silmaril.Wasm.V2.RefType} (hok : ElemModeOk C md rt) {cm : Silmaril.Wasm.ElemMode}
    (h : Silmaril.Wasm.V2.ElemMode.toCore md = some cm) : ElemMode.inFeatB v20 cm = true := by
  cases hok with
  | active _ _ hoff =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact constExpr_v20 hoff hb
  | passive =>
    cases h
    simp [ElemMode.inFeatB]
  | declare =>
    cases h
    simp [ElemMode.inFeatB]

theorem elem_v20 {C : Context} {e : Silmaril.Wasm.V2.Elem} {rt : Silmaril.Wasm.V2.RefType}
    (hok : ElemOk C e rt) {ce : Silmaril.Wasm.Elem}
    (h : Silmaril.Wasm.V2.Elem.toCore e = some ce) : Elem.inFeatB v20 ce = true := by
  simp only [Silmaril.Wasm.V2.Elem.toCore, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at h
  obtain ⟨init, hinit, md, hmd, rfl⟩ := h
  obtain ⟨rfl, hexprs, hmode⟩ := hok
  have hi : init.all (constExprB v20) = true :=
    mapM_all hinit fun ex hex _ hy => constExpr_v20 (hexprs ex hex) hy
  simp [Elem.inFeatB, refType_v20, hi, elemMode_v20 hmode hmd]

theorem data_v20 {C : Context} {d : Silmaril.Wasm.V2.Data} (hok : DataOk C d)
    {cd : Silmaril.Wasm.Data} (h : Silmaril.Wasm.V2.Data.toCore d = some cd) :
    Data.inFeatB v20 cd = true := by
  rcases d with ⟨bytes, mode⟩
  obtain ⟨md, hmd, rfl⟩ := Option.map_eq_some_iff.mp h
  cases hok with
  | active hx _ hoff =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hmd
    simp [Data.inFeatB, DataMode.inFeatB, memIdxB, hx, constExpr_v20 hoff hb]
  | passive =>
    cases hmd
    simp [Data.inFeatB, DataMode.inFeatB]

/-- Memory imports of the image are counted by the memories of the import types. -/
theorem memImports {Δ : Context} :
    ∀ {is : List Silmaril.Wasm.V2.Import} {ixt : List Silmaril.Wasm.V2.ExternType},
      List.Forall₂ (ImportOk Δ) is ixt →
        ((is.map Silmaril.Wasm.V2.Import.toCore).filter Import.isMemory).length =
          (Silmaril.Wasm.V2.ExternType.mems ixt).length
  | _, _, .nil => rfl
  | i :: _, _, .cons hok hrest => by
    have ih := memImports hrest
    rcases i with ⟨_, _, d⟩
    cases d <;> (obtain ⟨hty, -⟩ := hok; simp [Silmaril.Wasm.V2.Module.importType?] at hty) <;>
      (obtain ⟨_, -, rfl⟩ := hty
       simpa [Silmaril.Wasm.V2.ExternType.mems, Import.isMemory, Silmaril.Wasm.V2.Import.toCore,
         List.filter_cons, Silmaril.Wasm.V2.ImportDesc.toCore] using ih)

/-- At most one memory, counting imports. -/
theorem mems_le {m : Silmaril.Wasm.V2.Module} {ixt xt : List Silmaril.Wasm.V2.ExternType}
    (h : ModuleOk m ixt xt) :
    (m.memories.map Silmaril.Wasm.V2.MemoryType.toCore).length +
      ((m.imports.map Silmaril.Wasm.V2.Import.toCore).filter Import.isMemory).length ≤ 1 := by
  cases h with
  | mk _ himports _ _ hmems _ _ _ _ _ hle _ hC _ =>
    subst hC
    have e₁ := memImports himports
    have e₂ := List.Forall₂.length_eq hmems
    simp only [List.length_append] at hle
    simp only [List.length_map, e₁]
    omega

/-- The section-wise facts of the image of a valid module. -/
theorem sections_v20 {m : Silmaril.Wasm.V2.Module} {ixt xt : List Silmaril.Wasm.V2.ExternType}
    (h : ModuleOk m ixt xt) {gs : List Silmaril.Wasm.Global} {fs : List Silmaril.Wasm.Func}
    {es : List Silmaril.Wasm.Elem} {ds : List Silmaril.Wasm.Data}
    (hg : m.globals.mapM Silmaril.Wasm.V2.Global.toCore = some gs)
    (hf : m.funcs.mapM Silmaril.Wasm.V2.Func.toCore = some fs)
    (he : m.elems.mapM Silmaril.Wasm.V2.Elem.toCore = some es)
    (hd : m.data.mapM Silmaril.Wasm.V2.Data.toCore = some ds) :
    gs.all (Global.inFeatB v20) = true ∧ fs.all (Func.inFeatB v20) = true ∧
      es.all (Elem.inFeatB v20) = true ∧ ds.all (Data.inFeatB v20) = true := by
  cases h with
  | mk _ _ hglobals _ _ helems hdatas _ _ _ _ _ _ _ =>
    refine ⟨mapM_all hg fun g hgm _ hy => ?_, mapM_all hf fun _ _ _ hy => func_v20 hy,
      mapM_all he fun e hem _ hy => ?_, mapM_all hd fun d hdm _ hy => data_v20 (hdatas d hdm) hy⟩
    · obtain ⟨gt, hok⟩ := forall₂_left hglobals g hgm
      exact global_v20 hok hy
    · obtain ⟨rt, hok⟩ := forall₂_left helems e hem
      exact elem_v20 hok hy

/-- **The Core image of a valid 2.0 module is in `v20`.** -/
theorem module_inFeat {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    {ixt xt : List Silmaril.Wasm.V2.ExternType} (h : ModuleOk m ixt xt)
    (hc : Silmaril.Wasm.V2.Module.toCore m = some cm) : Module.InFeat v20 cm := by
  simp only [Silmaril.Wasm.V2.Module.toCore, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hc
  obtain ⟨gs, hg, fs, hf, es, he, ds, hd, rfl⟩ := hc
  obtain ⟨hgs, hfs, hes, hds⟩ := sections_v20 h hg hf he hd
  have hmem := mems_le h
  rw [List.length_map] at hmem
  simp [Module.InFeat, Module.inFeatB, List.all_map, Function.comp_def, recType_v20, import_v20,
    memoryType_v20, table_v20, hgs, hfs, hes, hds]
  exact Or.inl hmem

/-- **The Core image of a valid 2.0 module is a valid module of `v20`.** -/
theorem validIn_image {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    (h : ModuleValid m) (hc : Silmaril.Wasm.V2.Module.toCore m = some cm) : ValidIn v20 cm := by
  obtain ⟨ixt, xt, hok⟩ := h
  exact ⟨Silmaril.Wasm.V2.Validation.ModuleValid.toCore hc ⟨ixt, xt, hok⟩, module_inFeat hok hc⟩

end Silmaril.Proofs.Wasm.Models.V2Core
