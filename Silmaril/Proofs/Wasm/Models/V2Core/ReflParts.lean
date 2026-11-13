module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflSections3

/-!
# Module-level facts for reflecting `Module_ok`

* `toCore_parts`: the sections of the Core image of a 2.0 module;
* `inFeat_globals`, `inFeat_elems`, `inFeat_data`, `inFeat_mems`: what `Module.InFeat v20` says
  about constant expressions (single instructions, since `v20` has no extended constants), data
  segments (memory `0`) and memories (at most one, counting imports);
* `globals_const`, `elems_const`: the constant expressions of a module, read back as 2.0
  constant expressions in the imported-globals context. These only need the globals to be a
  prefix, not the `REFS` of the context, so they come before the `REFS` equation
  `funcIdxNonFuncs_toCore`;
* `func_type`, `elem_type`: the Core types of functions and element segments are images.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)
open Silmaril.Wasm.Models

/-- The sections of the Core image of a 2.0 module. -/
theorem toCore_parts {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    (hc : Silmaril.Wasm.V2.Module.toCore m = some cm) :
    ∃ cg cf ce cd, m.globals.mapM Silmaril.Wasm.V2.Global.toCore = some cg ∧
      m.funcs.mapM Silmaril.Wasm.V2.Func.toCore = some cf ∧
      m.elems.mapM Silmaril.Wasm.V2.Elem.toCore = some ce ∧
      m.data.mapM Silmaril.Wasm.V2.Data.toCore = some cd ∧
      cm = { types := m.types.map Silmaril.Wasm.V2.FuncType.toCoreRec
             imports := m.imports.map Silmaril.Wasm.V2.Import.toCore
             tags := []
             globals := cg
             memories := m.memories.map Silmaril.Wasm.V2.MemoryType.toCore
             tables := m.tables.map Silmaril.Wasm.V2.TableType.toCoreTable
             funcs := cf
             data := cd
             elems := ce
             start := m.start
             exports := m.exports.map Silmaril.Wasm.V2.Export.toCore } := by
  simp only [Silmaril.Wasm.V2.Module.toCore, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hc
  obtain ⟨cg, hcg, cf, hcf, ce, hce, cd, hcd, e⟩ := hc
  exact ⟨cg, cf, ce, cd, hcg, hcf, hce, hcd, e.symm⟩

/-! ## What `v20` says -/

theorem v20_extConst : v20.has .extConst = false := by decide

theorem v20_multiMemory : v20.has .multiMemory = false := by decide

/-- A constant expression of `v20` is a simple one. -/
theorem simple_of_constExprB {e : List Silmaril.Wasm.Instr} (h : constExprB v20 e = true) :
    simpleConst e = true := by
  simp only [constExprB, Bool.and_eq_true, Bool.or_eq_true, v20_extConst] at h
  simpa using h.2

theorem inFeat_globals {cm : Silmaril.Wasm.Module} (h : Module.InFeat v20 cm) :
    ∀ g ∈ cm.globals, simpleConst g.init = true := by
  intro g hg
  simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true, List.all_eq_true] at h
  exact simple_of_constExprB (by
    have := h.1.1.1.1.1.1.1.2 g hg
    simp only [Global.inFeatB, Bool.and_eq_true] at this
    exact this.2)

theorem inFeat_elems {cm : Silmaril.Wasm.Module} (h : Module.InFeat v20 cm) :
    ∀ e ∈ cm.elems, (∀ ex ∈ e.init, simpleConst ex = true) ∧
      ∀ x off, e.mode = .active x off → simpleConst off = true := by
  intro e he
  simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true, List.all_eq_true] at h
  have hel := h.1.1.1.2 e he
  simp only [Elem.inFeatB, Bool.and_eq_true, List.all_eq_true] at hel
  refine ⟨fun ex hex => simple_of_constExprB (hel.1.2 ex hex), fun x off hm => ?_⟩
  have hmd := hel.2
  rw [hm] at hmd
  exact simple_of_constExprB hmd

theorem inFeat_data {cm : Silmaril.Wasm.Module} (h : Module.InFeat v20 cm) :
    ∀ d ∈ cm.data, ∀ x off, d.mode = .active x off → x.toNat = 0 ∧ simpleConst off = true := by
  intro d hd x off hm
  simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true, List.all_eq_true] at h
  have hda := h.1.1.2 d hd
  simp only [Data.inFeatB, hm, DataMode.inFeatB, memIdxB, Bool.and_eq_true, Bool.or_eq_true,
    v20_multiMemory, beq_iff_eq] at hda
  exact ⟨by simpa using hda.1.2, simple_of_constExprB hda.2⟩

theorem inFeat_mems {cm : Silmaril.Wasm.Module} (h : Module.InFeat v20 cm) :
    cm.memories.length + (cm.imports.filter Import.isMemory).length ≤ 1 := by
  simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true, Bool.or_eq_true,
    v20_multiMemory, decide_eq_true_eq] at h
  simpa using h.1.2

/-! ## Constant expressions before `REFS` -/

/-- The global initialisers are 2.0 constant expressions over the imported globals. -/
theorem globals_const {Cp : VCtx} {D : KCtx} (hpre : Cp.globals.map globalToC <+: D.globals)
    {gs : List Silmaril.Wasm.V2.Global} {cgs : List Silmaril.Wasm.Global}
    {gts : List Silmaril.Wasm.Validation.CGlobalType}
    (hm : gs.mapM Silmaril.Wasm.V2.Global.toCore = some cgs)
    (h : Silmaril.Wasm.Validation.GlobalsOk D cgs gts)
    (hs : ∀ g ∈ gs, ∀ cg, Silmaril.Wasm.V2.Global.toCore g = some cg → simpleConst cg.init = true)
    (hb : ∀ g ∈ gs, ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < Cp.globals.length) :
    ∀ g ∈ gs, Silmaril.Wasm.V2.Validation.ExprConst Cp g.init := by
  have hall := (forall₂_mapM_eq (g := fun g => globalToC g.type)
    (P := fun g => (∀ cg, Silmaril.Wasm.V2.Global.toCore g = some cg → simpleConst cg.init = true) →
      (∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < Cp.globals.length) →
      Silmaril.Wasm.V2.Validation.ExprConst Cp g.init) (fun g cg gt hcg hr => by
        obtain ⟨G, hG, -, hok⟩ := hr
        refine ⟨global_type hcg hok, fun hs' hb' => ?_⟩
        obtain ⟨init, hinit, rfl⟩ := Option.map_eq_some_iff.mp hcg
        exact exprConst_refl (hpre.trans hG) hinit (hs' _ hcg) hok.2.2.const hb')
    hm (globalsOk_each h)).2
  exact fun g hg => hall g hg (hs g hg) (hb g hg)

/-- The Core type of an element segment of the image is the image of its type. -/
theorem elem_type {D : KCtx} {e : Silmaril.Wasm.V2.Elem} {ce : Silmaril.Wasm.Elem}
    (hce : Silmaril.Wasm.V2.Elem.toCore e = some ce) {rt : Silmaril.Wasm.Validation.CRefType}
    (h : Silmaril.Wasm.Validation.ElemOk D ce rt) : rt = e.type.toC := by
  obtain ⟨init, -, hce'⟩ := Option.bind_eq_some_iff.mp hce
  obtain ⟨cmode, -, rfl⟩ := Option.map_eq_some_iff.mp hce'
  exact h.1.trans (Silmaril.Wasm.V2.Validation.closeRef_toCore D e.type)

/-- The expressions of an element segment are 2.0 constant expressions. -/
theorem elem_const {Cp : VCtx} {D : KCtx} (hpre : Cp.globals.map globalToC <+: D.globals)
    {e : Silmaril.Wasm.V2.Elem} {ce : Silmaril.Wasm.Elem}
    (hce : Silmaril.Wasm.V2.Elem.toCore e = some ce) {rt : Silmaril.Wasm.Validation.CRefType}
    (h : Silmaril.Wasm.Validation.ElemOk D ce rt)
    (hsi : ∀ ex ∈ ce.init, simpleConst ex = true)
    (hso : ∀ x off, ce.mode = .active x off → simpleConst off = true)
    (hbi : ∀ ex ∈ e.init, ∀ y, Silmaril.Wasm.V2.Instr.globalGet y ∈ ex → y.toNat < Cp.globals.length)
    (hbo : ∀ x off, e.mode = .active x off →
      ∀ y, Silmaril.Wasm.V2.Instr.globalGet y ∈ off → y.toNat < Cp.globals.length) :
    (∀ ex ∈ e.init, Silmaril.Wasm.V2.Validation.ExprConst Cp ex) ∧
      ∀ x off, e.mode = .active x off → Silmaril.Wasm.V2.Validation.ExprConst Cp off := by
  obtain ⟨init, hinit, hce'⟩ := Option.bind_eq_some_iff.mp hce
  obtain ⟨cmode, hcmode, rfl⟩ := Option.map_eq_some_iff.mp hce'
  refine ⟨fun ex hex => ?_, fun x off hm => ?_⟩
  · obtain ⟨ex', hex', hmem⟩ := mapM_mem_of hinit ex hex
    exact exprConst_refl hpre hex' (hsi ex' hmem) (h.2.2.1 ex' hmem).const (hbi ex hex)
  · rw [hm] at hcmode
    obtain ⟨off', hoff', rfl⟩ := Option.map_eq_some_iff.mp hcmode
    have hmo := h.2.2.2
    cases hmo with
    | active _ _ ho => exact exprConst_refl hpre hoff' (hso x off' rfl) ho.const (hbo x off hm)

/-- The Core type of a function of the image is the defined type of a 2.0 function type. -/
theorem func_type {C : KCtx} {types : List Silmaril.Wasm.V2.FuncType}
    (ht : C.types = types.map Silmaril.Wasm.V2.FuncType.toDefType) {f : Silmaril.Wasm.V2.Func}
    {b : Silmaril.Wasm.Func} (hb : Silmaril.Wasm.V2.Func.toCore f = some b)
    {d : Silmaril.Wasm.Validation.DefType} (h : Silmaril.Wasm.Validation.FuncOk C b d) :
    ∃ ft : Silmaril.Wasm.V2.FuncType, (∃ b', Silmaril.Wasm.V2.Func.toCore f = some b' ∧
      Silmaril.Wasm.Validation.FuncOk C b' ft.toDefType) ∧ d = ft.toDefType := by
  have hd : C.types[b.type.toNat]? = some d := by cases h; assumption
  rw [ht] at hd
  obtain ⟨ft, -, e⟩ := getElem?_map_some hd
  exact ⟨ft, ⟨b, hb, e ▸ h⟩, e.symm⟩

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
