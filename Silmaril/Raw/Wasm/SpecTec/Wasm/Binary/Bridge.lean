module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Agreement
public import Silmaril.Wasm.Versions.Thms
-- Hand copy: source namespaces kept, only import lines rewritten
-- (imports of other topics' Raw modules go through their public headers).

/-! # Bridging `toCore` and `toCoreBinary`: validation

The binary agreement theorems (`Binary/Agreement.lean`) are stated for
`toCoreBinary`, the embedding with the element types that Core 3.0 decodes
(`(ref func)`), while the Lime1/V1 → Core validation and instantiation
correspondences are stated for `toCore` (`funcref`). The two embeddings differ only
in element-segment types (`Lime1.Module.toCore_eq_retype`), and `ofCore?` retracts
both (`Module.ofCore?_toCore`, `Module.ofCore?_toCoreBinary`).

This file proves that validity carries over, so that "Core decodes these V1/Lime1
bytes to a valid module" holds end to end: `(ref func)` element segments are valid
in a `funcref` table, since `(ref func) <: (ref null func)`
(`Lime1.Validation.ModuleValid.toCoreBinary_ok`, `ModuleValid.toCoreBinary` for
Lime1 and V1).

Instantiation (`Lime1.Execution.Instantiation.toCoreBinary`,
`InstantiationDiverges.toCoreBinary`) is in `Binary/BridgeInstantiation.lean`:
element types are not observed by Lime1 programs (Lime1 has no
`table.init`/`elem.drop`), and `ToCore.Store.erase` forgets element instances.

The alternative, changing `Elem.toCore` itself to `(ref func)` and deleting
`toCoreBinary`, is recorded in `docs/projects/wasm.md` (Open questions).
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Validation

open Silmaril.Wasm.Validation

/-- The Core reference type `(ref func)` that the binary format assigns to legacy
element segments. -/
abbrev refFuncC : CRefType := .ref false (.abs .func)

theorem funcIdxNonFuncs_toCoreBinary (m : Module) :
    funcIdxNonFuncs m.toCoreBinary = funcIdxNonFuncs m.toCore := by
  simp [funcIdxNonFuncs, Module.toCoreBinary, Module.toCore, Elem.toCoreBinary,
    List.flatMap_map]

/-- `ref.func x` has type `(ref func)` (not only `funcref`). -/
theorem refFunc_ok_nonnull (C : Wasm.Validation.Context) {x : FuncIdx} {ft : FuncType}
    (hf : C.funcs[x.toNat]? = some ft.toDefType) (hr : x.toNat ∈ C.refs) :
    ExprOkConst C [.refFunc x] (.refv refFuncC) := by
  refine ⟨?_, ?_⟩
  · have h1 := single_plain (C := C) (.reference (.refFunc hf hr))
      (by intro t ht; simp at ht; subst ht
          exact .refv (.ref (.use (.dt (tyOk_toDefType _ _)))))
    refine InstrsOk.sub h1 ⟨.nil, ?_, by simp⟩ ⟨by simp [ResultOk], ?_, by simp⟩
    · exact .cons (.refv (.refNonNull (.defFunc (expand_toDefType ft)))) .nil
    · intro t ht; simp at ht; subst ht; exact .refv (.ref (.abs _))
  · intro i hi
    simp at hi; subst hi; exact .refFunc _

/-- A valid Lime1 module's binary-faithful image is a valid Core module,
with the same import types as `toCore_ok`.

The proof follows `ModuleValid.toCore_ok`; only the element segments (and hence the
context's `elems`) differ: they are typed `(ref func)`, which is valid in the `funcref`
tables since `(ref func) <: (ref null func)`, and every initializer `ref.func x` has
type `(ref func)`. -/
theorem Silmaril.Wasm.Validation.ModuleValid.toCoreBinary_ok {m : Module} (h : Silmaril.Wasm.Validation.ModuleValid m) :
    ∃ xtE, Wasm.Validation.ModuleOk m.toCoreBinary
      ⟨m.imports.map fun i => importC m.types i.desc, xtE⟩ := by
  -- Core index spaces
  let dts := m.types.map V1.FuncType.toDefType
  let xtI := m.imports.map fun i => importC m.types i.desc
  let fdts := (m.funcs.filterMap fun f => m.types[f.type.toNat]?).map V1.FuncType.toDefType
  let gts := m.globals.map fun g => globalToC g.type
  let tts := m.tables.map tableToC
  let rts := m.elems.map fun _ => refFuncC
  let C' : Wasm.Validation.Context :=
    { types := dts, globals := CExternType.globals xtI,
      funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m.toCoreBinary }
  let C : Wasm.Validation.Context :=
    { C' with
      tags := CExternType.tags xtI ++ [], globals := C'.globals ++ gts,
      mems := CExternType.mems xtI ++ m.toCore.memories,
      tables := CExternType.tables xtI ++ tts,
      datas := m.toCore.data.map fun _ => (), elems := rts }
  have hfuncs_eq : (moduleContext m).funcs.map V1.FuncType.toDefType = C.funcs := by
    simp only [C, C', moduleContext, List.map_append, fdts]
    rw [xt_funcs m.types m.imports h.imports]
    rfl
  have hA : Agrees (moduleContext m) C := by
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · exact List.prefix_refl _
    · rw [hfuncs_eq]
    · simp only [C, moduleContext, List.map_append, tts]
      rw [xt_tables m.types m.imports]
      exact List.prefix_refl _
    · simp only [C, moduleContext, List.map_append, Module.toCore]
      rw [xt_mems m.types m.imports]
      exact List.prefix_refl _
    · simp only [C, C', moduleContext, List.map_append, gts, List.map_map]
      rw [xt_globals m.types m.imports]
      simp only [importedGlobals]
      exact List.prefix_refl _
  have hAinit : ∀ D : Wasm.Validation.Context,
      (importedGlobals m).map globalToC <+: D.globals → D.locals = [] → D.labels = [] →
      D.return_ = none → Agrees (initializerContext m) D := by
    intro D hg hl hlab hr
    exact ⟨by simp [initializerContext], by simp [initializerContext],
      by simp [initializerContext], by simp [initializerContext], hg,
      by simp [initializerContext, hl], by simp [initializerContext, hlab],
      by simp [initializerContext, hr]⟩
  have hglobals : ∀ (gs : List Global) (D : Wasm.Validation.Context),
      (∀ g ∈ gs, GlobalValid (initializerContext m) g) →
      (importedGlobals m).map globalToC <+: D.globals → D.locals = [] → D.labels = [] →
      D.return_ = none →
      GlobalsOk D (gs.map Global.toCore) (gs.map fun g => globalToC g.type) := by
    intro gs
    induction gs with
    | nil => intro D _ _ _ _ _; exact .nil
    | cons g gs ih =>
      intro D hv hg hl hlab hr
      refine .cons ⟨(closeGlobalType_toCore _ _).symm, .num _, ?_⟩
        (ih _ (fun g' hg' => hv g' (by simp [hg'])) (hg.trans (List.prefix_append _ _))
          hl hlab hr)
      exact constExpr_toCore (hAinit D hg hl hlab hr) (hv g (by simp))
  have hexports : ∀ e ∈ m.toCore.exports, ∃ xt, ExportOk C e xt := by
    intro e he
    simp only [Module.toCore, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨et, het⟩ := h.exports e₀ he₀
    rcases e₀ with ⟨nm, idx⟩
    cases idx with
    | func i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨ft, hft, -⟩ := het
      exact ⟨.func ft.toDefType, .func (prefix_map_getElem? hA.funcs hft)⟩
    | table i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨tt, htt, -⟩ := het
      exact ⟨.table (tableToC tt), .table (prefix_map_getElem? hA.tables htt)⟩
    | memory i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨mt, hmt, -⟩ := het
      exact ⟨.mem mt.toCore, .mem (prefix_map_getElem? hA.mems hmt)⟩
    | global i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨gt, hgt, -⟩ := het
      exact ⟨.global (globalToC gt), .global (prefix_map_getElem? hA.globals hgt)⟩
  obtain ⟨xtE, hxtE⟩ := forall₂_exists_of _ hexports
  have himports : List.Forall₂ (ImportOk { types := dts }) m.toCore.imports xtI :=
    forall₂_map_of _ _ m.imports (fun i hi => importOk_toCore m.types i (h.imports i hi))
  have hglobals' : GlobalsOk C' m.toCore.globals gts := by
    refine hglobals m.globals C' h.globals ?_ rfl rfl rfl
    show _ <+: CExternType.globals xtI
    rw [xt_globals]
    exact List.prefix_refl _
  have hmems : ∀ mt ∈ m.toCore.memories, MemOk mt := by
    intro mt hmt
    simp only [Module.toCore, List.mem_map] at hmt
    obtain ⟨mt₀, hmt₀, rfl⟩ := hmt
    exact memTypeOk_toCore (h.memories mt₀ hmt₀)
  have htables : List.Forall₂ (TableOk C') m.toCore.tables tts :=
    forall₂_map_of tableToCore tableToC m.tables
      (fun t ht => ⟨rfl, tableTypeOk_toCore _ (h.tables t ht), refNull_ok C'⟩)
  have hfuncs : List.Forall₂ (FuncOk C) m.toCore.funcs fdts := by
    refine forall₂_filterMap_of Func.toCore _ V1.FuncType.toDefType m.funcs ?_
    intro f hf
    obtain ⟨ft, hft, -, hbody⟩ := h.functions f hf
    refine ⟨ft, hft, ?_⟩
    have hd : C.type? (Func.toCore f).type = some ft.toDefType := by
      simp only [Wasm.Validation.Context.type?, C, C', dts, Func.toCore, List.getElem?_map]
      rw [show m.types[f.type.toNat]? = some ft from hft]; rfl
    have hAf : Agrees (functionContext (moduleContext m) ft f.locals)
        (C.funcBody (ft.params.map Silmaril.Wasm.Validation.Ty.num) (ft.results.map Silmaril.Wasm.Validation.Ty.num)
          (f.locals.map fun t => ⟨.set, .num t⟩)) :=
      ⟨hA.types, hA.funcs, hA.tables, hA.mems, hA.globals,
        by simp [functionContext, Wasm.Validation.Context.funcBody, Function.comp_def],
        by simp [functionContext, Wasm.Validation.Context.funcBody],
        by simp [functionContext, Wasm.Validation.Context.funcBody]⟩
    refine FuncOk.mk (lts := f.locals.map fun t => ⟨.set, .num t⟩) hd (expand_toDefType ft) ?_ ?_
    · exact forall₂_map_of _ _ f.locals (fun t _ => LocalOk.set (.num t) trivial)
    · simpa [ExprOk, Silmaril.Wasm.Validation.Ty.toList_ofList, Func.toCore] using ExprType.toCore' hAf hbody
  have hdata : ∀ d ∈ m.toCore.data, DataOk C d := by
    intro d hd
    simp only [Module.toCore, List.mem_map] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    obtain ⟨⟨mt, hmt⟩, hoff⟩ := h.data d₀ hd₀
    exact DataModeOk.active (prefix_map_getElem? hA.mems hmt) (constExpr_toCore hA hoff)
  have helems : List.Forall₂ (ElemOk C) m.toCoreBinary.elems rts := by
    refine forall₂_map_of Elem.toCoreBinary (fun _ => refFuncC) m.elems ?_
    intro e he
    obtain ⟨⟨tt, htt⟩, hoff, hfs⟩ := h.elements e he
    refine ⟨rfl, .ref (.abs _), ?_, ?_⟩
    · intro ex hex
      simp only [Elem.toCoreBinary, Elem.toCore, List.mem_map] at hex
      obtain ⟨f, hf, rfl⟩ := hex
      obtain ⟨ft, hft⟩ := hfs f hf
      refine refFunc_ok_nonnull C (prefix_map_getElem? hA.funcs hft) ?_
      show _ ∈ funcIdxNonFuncs m.toCoreBinary
      rw [funcIdxNonFuncs_toCoreBinary]
      exact mem_refs_of_elem he hf
    · exact ElemModeOk.active (prefix_map_getElem? hA.tables htt)
        (.refNull .heapRefl) (constExpr_toCore hA hoff)
  have hstart : ∀ x, m.toCore.start = some x → StartOk C x := by
    intro x hx
    have := h.start x hx
    exact ⟨_, prefix_map_getElem? hA.funcs this, by simpa using expand_toDefType ⟨[], []⟩⟩
  have hdisjoint : (m.toCore.exports.map Wasm.Export.name).Nodup := by
    simpa [Module.toCore, V1.Export.toCore, Function.comp_def] using h.uniqueExports
  exact ⟨xtE, ModuleOk.mk (jts := []) (typesOk_map m.types {}) himports rfl rfl .nil
    hglobals' hmems htables hfuncs hdata helems hstart hxtE hdisjoint⟩

theorem Silmaril.Wasm.Validation.ModuleValid.toCoreBinary {m : Module} (h : Silmaril.Wasm.Validation.ModuleValid m) :
    Wasm.Validation.ModuleValid m.toCoreBinary :=
  let ⟨_, hok⟩ := Silmaril.Wasm.Validation.ModuleValid.toCoreBinary_ok h
  ⟨_, hok⟩

end Silmaril.Wasm.Lime1.Validation

namespace Silmaril.Wasm.V1.Validation

/-- Through Lime1 (`ModuleValid.toLime`, `Module.toLime_toCoreBinary`). -/
theorem Silmaril.Wasm.Validation.ModuleValid.toCoreBinary {m : Module} (h : Silmaril.Wasm.Validation.ModuleValid m) :
    Wasm.Validation.ModuleValid m.toCoreBinary := by
  have := Lime1.Validation.ModuleValid.toCoreBinary (Silmaril.Wasm.Validation.ModuleValid.toLime h)
  simpa using this

end Silmaril.Wasm.V1.Validation
