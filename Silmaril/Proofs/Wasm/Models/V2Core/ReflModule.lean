module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflParts

/-!
# Validity of 2.0 modules is reflected by the Core image (under `ConstReadsImports`)

**`refl_valid`**: if the Core 3.0 image of a Wasm 2.0 module is a valid module of `v20`
(`ValidIn v20`), and every `global.get` in its constant expressions reads an imported global
(`ConstBound`, the statement of `ConstReadsImports`), then the 2.0 module is valid.

The proof reads every premise of Core's `Module_ok` back as the 2.0 premise:

* the type section and the imports are images (`types_refl`, `imports_refl`);
* the Core types of globals, tables and element segments are images, so the Core module
  context `C` is the image of the 2.0 module context (`Rel`), and the Core context `C'` of the
  global initialisers agrees with 2.0's `C'` on functions and imported globals (`RelK`);
* `REFS` agree (`funcIdxNonFuncs_toCore`, from the 2.0 constant expressions `globals_const`,
  `elem_const`);
* each item reflects (`globals_refl`, `elem_one`, `data_one`, `func_one`, `start_one`,
  `exports_refl`), and the memory bound and export names come from `v20` and Core.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)
open Silmaril.Wasm.Models

/-- Every `global.get` in a constant expression of `m` reads an imported global (the statement
of `Silmaril.Wasm.Models.V2Core.ConstReadsImports`). -/
def ConstBound (m : Silmaril.Wasm.V2.Module) : Prop :=
  ∀ e ∈ m.globals.map (·.init) ++ m.elems.flatMap (·.init) ++
      m.elems.filterMap (fun e => match e.mode with | .active _ off => some off | _ => none) ++
      m.data.filterMap (fun d => match d.mode with | .active _ off => some off | _ => none),
    ∀ x, .globalGet x ∈ e →
      x.toNat < (m.imports.filter fun i => match i.desc with | .global _ => true | _ => false).length

/-- The four kinds of constant expression of `ConstBound`. -/
theorem constBound_parts {m : Silmaril.Wasm.V2.Module} (h : ConstBound m) {n : Nat}
    (hn : (m.imports.filter fun i => match i.desc with | .global _ => true | _ => false).length = n) :
    (∀ g ∈ m.globals, ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < n) ∧
    (∀ e ∈ m.elems, ∀ ex ∈ e.init, ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ ex → x.toNat < n) ∧
    (∀ e ∈ m.elems, ∀ y off, e.mode = .active y off →
      ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ off → x.toNat < n) ∧
    (∀ d ∈ m.data, ∀ y off, d.mode = .active y off →
      ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ off → x.toNat < n) := by
  subst hn
  refine ⟨fun g hg => h _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map_of_mem hg)))), fun e he ex hex => h _ ?_,
    fun e he y off hm => h _ ?_, fun d hd y off hm => h _ ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨e, he, hex⟩)))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_filterMap.mpr ⟨e, he, by simp [hm]⟩))
  · exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨d, hd, by simp [hm]⟩)

/-- 2.0's `C'` of `Module_ok`: imported globals only. -/
def ctxConst (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) : VCtx :=
  { types := m.types
    funcs := Silmaril.Wasm.V2.ExternType.funcs ixt ++ ft
    globals := Silmaril.Wasm.V2.ExternType.globals ixt
    tables := Silmaril.Wasm.V2.ExternType.tables ixt ++ m.tables
    mems := Silmaril.Wasm.V2.ExternType.mems ixt ++ m.memories
    refs := Silmaril.Wasm.V2.Validation.funcIdxNonFuncs m }

/-- 2.0's `C'` without tables and memories: the image of Core's `C'`. -/
def ctxConstK (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) : VCtx :=
  { types := m.types
    funcs := Silmaril.Wasm.V2.ExternType.funcs ixt ++ ft
    globals := Silmaril.Wasm.V2.ExternType.globals ixt
    refs := Silmaril.Wasm.V2.Validation.funcIdxNonFuncs m }

/-- 2.0's `C` of `Module_ok`. -/
def ctxMod (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) : VCtx :=
  { types := m.types
    funcs := Silmaril.Wasm.V2.ExternType.funcs ixt ++ ft
    globals := Silmaril.Wasm.V2.ExternType.globals ixt ++ m.globals.map (fun g => g.type)
    tables := Silmaril.Wasm.V2.ExternType.tables ixt ++ m.tables
    mems := Silmaril.Wasm.V2.ExternType.mems ixt ++ m.memories
    elems := m.elems.map (fun e => e.type)
    datas := m.data.map fun _ => ()
    refs := Silmaril.Wasm.V2.Validation.funcIdxNonFuncs m }

/-- Core's `C'` on the image (after the `REFS` equation). -/
def kConst (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) : KCtx :=
  { types := m.types.map Silmaril.Wasm.V2.FuncType.toDefType
    globals := Silmaril.Wasm.Validation.CExternType.globals (ixt.map Silmaril.Wasm.V2.ExternType.toCore)
    funcs := Silmaril.Wasm.Validation.CExternType.funcs (ixt.map Silmaril.Wasm.V2.ExternType.toCore) ++
      ft.map Silmaril.Wasm.V2.FuncType.toDefType
    refs := (Silmaril.Wasm.V2.Validation.funcIdxNonFuncs m).map Silmaril.Wasm.Idx.toNat }

/-- Core's `C` on the image (after the `REFS` equation). -/
def kMod (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) (cd : List Silmaril.Wasm.Data) : KCtx :=
  { kConst m ixt ft with
    tags := Silmaril.Wasm.Validation.CExternType.tags (ixt.map Silmaril.Wasm.V2.ExternType.toCore) ++ []
    globals := (kConst m ixt ft).globals ++ m.globals.map (fun x => globalToC x.type)
    mems := Silmaril.Wasm.Validation.CExternType.mems (ixt.map Silmaril.Wasm.V2.ExternType.toCore) ++
      m.memories.map Silmaril.Wasm.V2.MemoryType.toCore
    tables := Silmaril.Wasm.Validation.CExternType.tables (ixt.map Silmaril.Wasm.V2.ExternType.toCore) ++
      m.tables.map tableToC
    datas := cd.map fun _ => ()
    elems := m.elems.map (fun e => e.type.toC) }

theorem rel_kConst (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) : Rel (ctxConstK m ixt ft) (kConst m ixt ft) where
  types := rfl
  recs := rfl
  tags := rfl
  funcs := by
    simp [kConst, ctxConstK, Silmaril.Wasm.V2.Validation.cext_funcs]
  globals := Silmaril.Wasm.V2.Validation.cext_globals ixt
  tables := rfl
  mems := rfl
  elems := rfl
  datas := rfl
  locals := fun y => by simp [kConst, ctxConstK]
  labels := rfl
  return_ := rfl
  refs := rfl

theorem rel_kMod (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) {cd : List Silmaril.Wasm.Data}
    (hlen : cd.length = m.data.length) : Rel (ctxMod m ixt ft) (kMod m ixt ft cd) where
  types := rfl
  recs := rfl
  tags := by simp [kMod, Silmaril.Wasm.V2.Validation.cext_tags]
  funcs := by simp [kMod, kConst, ctxMod, Silmaril.Wasm.V2.Validation.cext_funcs]
  globals := by
    simp [kMod, kConst, ctxMod, Silmaril.Wasm.V2.Validation.cext_globals, Function.comp_def]
  tables := by simp [kMod, ctxMod, Silmaril.Wasm.V2.Validation.cext_tables]
  mems := by simp [kMod, ctxMod, Silmaril.Wasm.V2.Validation.cext_mems]
  elems := by simp [kMod, ctxMod, Function.comp_def]
  datas := units_eq hlen
  locals := fun y => by simp [kMod, kConst, ctxMod]
  labels := rfl
  return_ := rfl
  refs := rfl

theorem relK_kConst (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) : RelK (ctxConst m ixt ft) (kConst m ixt ft) :=
  RelK.of_rel (rel_kConst m ixt ft) rfl
    (by rw [show (kConst m ixt ft).globals = _ from Silmaril.Wasm.V2.Validation.cext_globals ixt]
        exact List.prefix_refl _) rfl

theorem relK_kMod (m : Silmaril.Wasm.V2.Module) (ixt : List Silmaril.Wasm.V2.ExternType)
    (ft : List Silmaril.Wasm.V2.FuncType) {cd : List Silmaril.Wasm.Data}
    (hlen : cd.length = m.data.length) : RelK (ctxConst m ixt ft) (kMod m ixt ft cd) :=
  RelK.of_rel (rel_kMod m ixt ft hlen) rfl
    ((relK_kConst m ixt ft).globals.trans (List.prefix_append _ _)) rfl

/-- The image of a member of a `mapM` source is a member of the image. -/
theorem mapM_mem_img {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') {a : α} (ha : a ∈ l) {b : β} (hb : f a = some b) : b ∈ l' := by
  obtain ⟨b', hb', hm⟩ := mapM_mem_of h a ha
  have e : b' = b := Option.some.inj (hb'.symm.trans hb)
  exact e ▸ hm

/-- **The 2.0 module of a valid `v20` Core image is valid** (under `ConstBound`). -/
theorem refl_valid {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    (hc : Silmaril.Wasm.V2.Module.toCore m = some cm) (hv : ValidIn v20 cm) (hcr : ConstBound m) :
    Silmaril.Wasm.V2.Validation.ModuleValid m := by
  obtain ⟨cg, cf, ce, cd, hcg, hcf, hce, hcd, rfl⟩ := toCore_parts hc
  obtain ⟨⟨_, hok⟩, hin⟩ := hv
  cases hok with
  | @mk dts xtI jts gts tts fdts rts xtE C' C htypes himports hC' hC htags hglobals hmems
      htables hfuncs hdata helems hstart hexports hdisjoint =>
  subst hC' hC
  have hdts : dts = m.types.map Silmaril.Wasm.V2.FuncType.toDefType := types_refl htypes
  subst hdts
  obtain ⟨ixt, himp, hxtI⟩ : ∃ ixt, List.Forall₂
      (Silmaril.Wasm.V2.Validation.ImportOk { types := m.types }) m.imports ixt ∧
      xtI = ixt.map Silmaril.Wasm.V2.ExternType.toCore := imports_refl himports
  subst hxtI
  have hjts : jts = [] := by cases htags; rfl
  subst hjts
  obtain ⟨ft, hfts, hfdts⟩ := forall₂_mapM_lift
    (fun _ _ _ hb hr => func_type rfl hb hr) hcf hfuncs
  subst hfdts
  have hgts : gts = m.globals.map (fun g => globalToC g.type) := (forall₂_mapM_eq (P := fun _ => True)
    (fun _ _ _ hcg hr => let ⟨_, _, _, hok⟩ := hr; ⟨global_type hcg hok, trivial⟩) hcg
    (globalsOk_each hglobals)).1
  have htts : tts = m.tables.map tableToC := (tables_refl htables).1
  have htabs : List.Forall₂ Silmaril.Wasm.V2.Validation.TableOk m.tables m.tables :=
    (tables_refl htables).2
  have hrts : rts = m.elems.map (fun e => e.type.toC) := (forall₂_mapM_eq (P := fun _ => True)
    (fun _ _ _ he hr => ⟨elem_type he hr, trivial⟩) hce helems).1
  subst hgts htts hrts
  -- the bounds of `ConstReadsImports`, against the imported globals
  have hlen : (Silmaril.Wasm.V2.ExternType.globals ixt).length =
      (m.imports.filter fun i => match i.desc with | .global _ => true | _ => false).length :=
    globals_count himp
  obtain ⟨hbg, hbi, hbo, hbd⟩ := constBound_parts hcr hlen.symm
  -- what `v20` says about the image
  have hsg : ∀ g ∈ m.globals, ∀ c, Silmaril.Wasm.V2.Global.toCore g = some c →
      simpleConst c.init = true := fun g hg c hc' =>
    inFeat_globals hin c (mapM_mem_img hcg hg hc')
  have hpre' : (ctxConst m ixt ft).globals.map globalToC <+:
      Silmaril.Wasm.Validation.CExternType.globals (ixt.map Silmaril.Wasm.V2.ExternType.toCore) := by
    rw [Silmaril.Wasm.V2.Validation.cext_globals]; exact List.prefix_refl _
  have hpre : (ctxConst m ixt ft).globals.map globalToC <+:
      Silmaril.Wasm.Validation.CExternType.globals (ixt.map Silmaril.Wasm.V2.ExternType.toCore) ++
        m.globals.map (fun g => globalToC g.type) := hpre'.trans (List.prefix_append _ _)
  -- the 2.0 constant expressions, and `REFS`
  have hgc : ∀ g ∈ m.globals, Silmaril.Wasm.V2.Validation.ExprConst (ctxConst m ixt ft) g.init :=
    globals_const hpre' hcg hglobals hsg hbg
  have hec : ∀ e ∈ m.elems, (∀ ex ∈ e.init, Silmaril.Wasm.V2.Validation.ExprConst (ctxConst m ixt ft) ex) ∧
      ∀ x off, e.mode = .active x off →
        Silmaril.Wasm.V2.Validation.ExprConst (ctxConst m ixt ft) off := fun e he => by
    obtain ⟨c, hc', hm⟩ := mapM_mem_of hce e he
    obtain ⟨rt, hrt⟩ := forall₂_left helems c hm
    obtain ⟨hsi, hso⟩ := inFeat_elems hin c hm
    exact elem_const hpre hc' hrt hsi hso (hbi e he) (hbo e he)
  have hrefs : _ = (Silmaril.Wasm.V2.Validation.funcIdxNonFuncs m).map Silmaril.Wasm.Idx.toNat :=
    Silmaril.Wasm.V2.Validation.funcIdxNonFuncs_toCore hc hgc
    (fun e he => (hec e he).1) (fun e he => (hec e he).2)
  rw [hrefs] at hglobals hfts hdata helems hstart hexports
  -- the image contexts
  have hlenD : cd.length = m.data.length :=
    (List.Forall₂.length_eq (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hcd)).symm
  have hRm : Rel (ctxMod m ixt ft) (kMod m ixt ft cd) := rel_kMod m ixt ft hlenD
  have hKc : RelK (ctxConst m ixt ft) (kConst m ixt ft) := relK_kConst m ixt ft
  have hKm : RelK (ctxConst m ixt ft) (kMod m ixt ft cd) := relK_kMod m ixt ft hlenD
  have htabEq : (kMod m ixt ft cd).tables = (ctxConst m ixt ft).tables.map tableToC := by
    simp [kMod, ctxConst, Silmaril.Wasm.V2.Validation.cext_tables]
  have hmemEq : (kMod m ixt ft cd).mems =
      (ctxConst m ixt ft).mems.map Silmaril.Wasm.V2.MemoryType.toCore := by
    simp [kMod, ctxConst, Silmaril.Wasm.V2.Validation.cext_mems]
  -- each section
  have hgok : ∀ g ∈ m.globals, Silmaril.Wasm.V2.Validation.GlobalOk (ctxConst m ixt ft) g g.type :=
    (globals_refl hKc hcg hglobals hsg hbg).2
  have helok : ∀ e ∈ m.elems, Silmaril.Wasm.V2.Validation.ElemOk (ctxConst m ixt ft) e e.type :=
    fun e he => by
      obtain ⟨c, hc', hm⟩ := mapM_mem_of hce e he
      obtain ⟨rt, hrt⟩ := forall₂_left helems c hm
      obtain ⟨hsi, hso⟩ := inFeat_elems hin c hm
      exact (elem_one hKm htabEq hc' hrt hsi hso (hbi e he) (hbo e he)).2
  have hdok : ∀ d ∈ m.data, Silmaril.Wasm.V2.Validation.DataOk (ctxConst m ixt ft) d :=
    fun d hd => by
      obtain ⟨c, hc', hm⟩ := mapM_mem_of hcd d hd
      exact data_one hKm hmemEq hc' (hdata c hm) (inFeat_data hin c hm) (hbd d hd)
  have hfok : List.Forall₂ (Silmaril.Wasm.V2.Validation.FuncOk (ctxMod m ixt ft)) m.funcs ft :=
    hfts.imp fun _ _ ⟨_, hb, hok⟩ => func_one hRm rfl rfl hb hok
  have hsok : ∀ x, m.start = some x → Silmaril.Wasm.V2.Validation.StartOk (ctxMod m ixt ft) x :=
    fun x hx => start_one hRm (hstart x hx)
  obtain ⟨xt, hxt⟩ := exports_refl hRm hexports
  have hle : (ctxMod m ixt ft).mems.length ≤ 1 := by
    have h₁ := inFeat_mems hin
    have h₂ := memImports himp
    simp only [List.length_map] at h₁
    simp only [ctxMod, List.length_append]
    omega
  have hnames : (m.exports.map Silmaril.Wasm.V2.Export.name).Nodup := by
    simpa [List.map_map, Function.comp_def, Silmaril.Wasm.V2.Export.toCore] using hdisjoint
  have htyok : List.Forall₂ Silmaril.Wasm.V2.Validation.TypeOk m.types m.types := by
    simpa using forall₂_map_self (f := id) fun t _ => ⟨rfl, trivial⟩
  exact ⟨ixt, xt, .mk htyok himp (forall₂_map_self hgok) htabs (mems_refl hmems)
    (forall₂_map_self helok) hdok hfok hsok hxt hle hnames rfl rfl⟩

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
