module

public import Silmaril.Wasm.Validation.Check.ModuleComplete
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Validation.RollClosed
public import Silmaril.Wasm.Validation.Subtyping.WeakenEmpty

@[expose] public section

/-! # Completeness of the module-validator assembly in well-formed contexts

`ModuleCheckers.Complete` asks each part checker to be complete in *every* context.
The concrete checkers are complete only in well-formed contexts without `RECS`
(instruction checking uses `Sub.check_complete`). `ModuleCheckers.CompleteWf`
guards every context-taking field by `C.Wf → C.recs = [] →` (and restricts `types`
to the empty context); `checkModule?_complete_wf` shows that every context
`checkModule?` builds from a `ModuleOk` derivation satisfies these guards.
-/

namespace Silmaril.Wasm.Validation

/-- Completeness of each part checker, in well-formed contexts with no `RECS`. -/
structure ModuleCheckers.CompleteWf (K : ModuleCheckers) : Prop where
  types : ∀ {rts dts}, TypesOk {} rts dts → K.types? {} rts = some dts
  import_ : ∀ {C im xt}, C.Wf → C.recs = [] → ImportOk C im xt → K.import? C im = some xt
  tag : ∀ {C x d}, C.Wf → C.recs = [] → TagOk C x d → K.tag? C x = some d
  globals : ∀ {C gs gts}, C.Wf → C.recs = [] → GlobalsOk C gs gts → K.globals? C gs = some gts
  mem : ∀ {mt}, MemOk mt → K.mem mt = true
  table : ∀ {C t tt}, C.Wf → C.recs = [] → TableOk C t tt → K.table? C t = some tt
  func : ∀ {C f d}, C.Wf → C.recs = [] → FuncOk C f d → K.func C f d = true
  data : ∀ {C d}, C.Wf → C.recs = [] → DataOk C d → K.data C d = true
  elem : ∀ {C e rt}, C.Wf → C.recs = [] → ElemOk C e rt → K.elem? C e = some rt
  start : ∀ {C x}, C.Wf → C.recs = [] → StartOk C x → K.start C x = true
  export_ : ∀ {C e xt}, C.Wf → C.recs = [] → ExportOk C e xt → K.export? C e = some xt

theorem ModuleCheckers.Complete.toCompleteWf {K : ModuleCheckers} (h : K.Complete) :
    K.CompleteWf :=
  ⟨h.types, fun _ _ => h.import_, fun _ _ => h.tag, fun _ _ => h.globals, h.mem,
    fun _ _ => h.table, fun _ _ => h.func, fun _ _ => h.data, fun _ _ => h.elem,
    fun _ _ => h.start, fun _ _ => h.export_⟩

namespace ModuleWf

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ b ∈ bs, ∃ a ∈ as, R a b
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right hs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem externs_tyOk {Δ : TypeCtx} : ∀ {xs : List CExternType}, (∀ xt ∈ xs, ExternTypeOk Δ xt) →
    (∀ d ∈ CExternType.tags xs, TyOk Δ d) ∧ (∀ g ∈ CExternType.globals xs, TyOk Δ g.type) ∧
      (∀ t ∈ CExternType.tables xs, TyOk Δ t.element) ∧ (∀ d ∈ CExternType.funcs xs, TyOk Δ d)
  | [], _ => by simp [CExternType.tags, CExternType.globals, CExternType.tables,
      CExternType.funcs]
  | x :: xs, h => by
    obtain ⟨i1, i2, i3, i4⟩ := externs_tyOk (xs := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    cases hx with
    | tag h' =>
      simp only [CExternType.tags, CExternType.globals, CExternType.tables, CExternType.funcs,
        List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨h'.1, i1⟩, i2, i3, i4⟩
    | global h' =>
      simp only [CExternType.tags, CExternType.globals, CExternType.tables, CExternType.funcs,
        List.mem_cons, forall_eq_or_imp]
      exact ⟨i1, ⟨h', i2⟩, i3, i4⟩
    | mem h' =>
      simp only [CExternType.tags, CExternType.globals, CExternType.tables, CExternType.funcs]
      exact ⟨i1, i2, i3, i4⟩
    | table h' =>
      simp only [CExternType.tags, CExternType.globals, CExternType.tables, CExternType.funcs,
        List.mem_cons, forall_eq_or_imp]
      exact ⟨i1, i2, ⟨h'.2, i3⟩, i4⟩
    | func h' _ =>
      simp only [CExternType.tags, CExternType.globals, CExternType.tables, CExternType.funcs,
        List.mem_cons, forall_eq_or_imp]
      exact ⟨i1, i2, i3, ⟨h', i4⟩⟩

theorem typeCtx_ok {rts : List RecType} {dts : List DefType} (h : TypesOk {} rts dts) :
    ({ types := dts } : TypeCtx).Ok := fun d hd =>
  have h0 := h.tyOk_empty' d hd
  ⟨SubClosed.closed_of_empty h0, wireCallRef_tyOk_of_empty _ h0⟩

theorem globalsOk_tyOk {Δ : TypeCtx} {C : Context} {gs : List Global} {gts : List CGlobalType}
    (h : GlobalsOk C gs gts) (hΔ : C.toTypeCtx = Δ) : ∀ g ∈ gts, TyOk Δ g.type := by
  induction h with
  | nil => simp
  | cons h _ ih =>
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hΔ ▸ h.2.1
    · exact ih hΔ g hg

theorem wf_empty {rts : List RecType} {dts : List DefType} (h : TypesOk {} rts dts) :
    ({ types := dts } : Context).Wf :=
  ⟨typeCtx_ok h, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem funcs_mem {C : Context} {fs : List Func} {fdts : List DefType}
    (h : List.Forall₂ (FuncOk C) fs fdts) : ∀ d ∈ fdts, d ∈ C.types := by
  intro d hd
  obtain ⟨_, _, hf⟩ := forall₂_mem_right h d hd
  cases hf with | mk hd' _ _ _ => exact List.mem_of_getElem? hd'

end ModuleWf

open ModuleWf in
theorem checkModule?_complete_wf {K : ModuleCheckers} {m : Module} {mt : CModuleType}
    (hK : K.CompleteWf) (h : ModuleOk m mt) : checkModule? K m = some mt := by
  obtain ⟨htypes, himports, rfl, rfl, htags, hglobals, hmems, htables, hfuncs, hdata,
    helems, hstart, hexports, hnd⟩ := h
  rename_i dts xtI jts gts tts fdts rts xtE
  have hΔ := typeCtx_ok htypes
  have hW0 : ({ types := dts } : Context).Wf := wf_empty htypes
  have hX := externs_tyOk (Δ := { types := dts }) (xs := xtI) (fun xt hxt => by
    obtain ⟨_, _, hi⟩ := forall₂_mem_right himports xt hxt
    exact hi.2)
  obtain ⟨hXt, hXg, hXtb, hXf⟩ := hX
  have hFd := funcs_mem hfuncs
  have hFty : ∀ d ∈ fdts, TyOk ({ types := dts } : TypeCtx) d := fun d hd =>
    (hΔ d (hFd d hd)).2
  have hfd : m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type) = some fdts :=
    List.mapM_some_of_forall₂ (fun _ _ hf => by
      cases hf with | mk hd _ _ _ => exact hd) hfuncs
  have hrts : rts = m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type :=
    List.Forall₂.eq_map (g := fun e => (moduleCtx' m dts xtI fdts).closeRef e.type)
      (fun _ _ he => he.1) helems
  subst hrts
  have htags' : List.Forall₂ (TagOk (moduleCtx' m dts xtI fdts)) m.tags jts := htags
  have hglobals' : GlobalsOk (moduleCtx' m dts xtI fdts) m.globals gts := hglobals
  have htables' : List.Forall₂ (TableOk (moduleCtx' m dts xtI fdts)) m.tables tts := htables
  have hW' : (moduleCtx' m dts xtI fdts).Wf := by
    refine ⟨hΔ, by simp [moduleCtx'], hXg, by simp [moduleCtx'], ?_, by simp [moduleCtx'],
      by simp [moduleCtx'], by simp [moduleCtx'], by simp [moduleCtx']⟩
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hXf d hd
    · exact hFty d hd
  have hr' : (moduleCtx' m dts xtI fdts).recs = [] := rfl
  generalize hCdef : moduleCtx m (moduleCtx' m dts xtI fdts) xtI jts gts tts
    (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type) = C
  have hW : C.Wf := by
    subst hCdef
    refine ⟨hΔ, ?_, ?_, ?_, ?_, by simp [moduleCtx, moduleCtx'], by simp [moduleCtx, moduleCtx'],
      by simp [moduleCtx, moduleCtx'], ?_⟩
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hXt d hd
      · obtain ⟨_, _, ht⟩ := forall₂_mem_right htags' d hd
        exact ht.2.1
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hXg g hg
      · exact globalsOk_tyOk hglobals' rfl g hg
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact hXtb t ht
      · obtain ⟨_, _, ht'⟩ := forall₂_mem_right htables' t ht
        exact ht'.2.1.2
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hXf d hd
      · exact hFty d hd
    · intro rt hrt
      obtain ⟨_, _, he⟩ := forall₂_mem_right helems rt hrt
      exact he.2.1
  have hr : C.recs = [] := by subst hCdef; rfl
  have hfuncs' : List.Forall₂ (FuncOk C) m.funcs fdts := hCdef ▸ hfuncs
  have hdata' : ∀ d ∈ m.data, DataOk C d := hCdef ▸ hdata
  have helems' : List.Forall₂ (ElemOk C) m.elems
      (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type) := hCdef ▸ helems
  have hstart' : ∀ x, m.start = some x → StartOk C x := hCdef ▸ hstart
  have hexports' : List.Forall₂ (ExportOk C) m.exports xtE := hCdef ▸ hexports
  have hc : (m.memories.all K.mem && allPairs (K.func C) m.funcs fdts &&
      m.data.all (K.data C) &&
      allPairs (fun e rt => K.elem? C e == some rt) m.elems
        (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type) &&
      m.start.all (K.start C)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨⟨fun x hx => hK.mem (hmems x hx),
      allPairs_complete (fun _ _ h => hK.func hW hr h) hfuncs'⟩,
      fun d hd => hK.data hW hr (hdata' d hd)⟩,
      allPairs_complete (fun _ _ he => by simp [hK.elem hW hr he]) helems'⟩, ?_⟩
    cases hs : m.start with
    | none => rfl
    | some x => simpa using hK.start hW hr (hstart' x hs)
  simp only [checkModule?, Option.bind_eq_bind, hK.types htypes,
    List.mapM_some_of_forall₂ (fun _ _ h => hK.import_ hW0 rfl h) himports, Option.bind_some,
    hfd,
    List.mapM_some_of_forall₂ (fun _ _ h => hK.tag hW' hr' h) htags', hK.globals hW' hr' hglobals',
    List.mapM_some_of_forall₂ (fun _ _ h => hK.table hW' hr' h) htables', hCdef, hc, ite_true,
    List.mapM_some_of_forall₂ (fun _ _ h => hK.export_ hW hr h) hexports', hnd]

theorem checkModule?_isSome_iff_wf {K : ModuleCheckers} {m : Module}
    (hS : K.Sound) (hC : K.CompleteWf) : (checkModule? K m).isSome ↔ ModuleValid m :=
  ⟨checkModuleValid_sound hS, fun ⟨_, h⟩ => by rw [checkModule?_complete_wf hC h]; rfl⟩

/-- Decidability of module validity from a sound set of part checkers that is complete
in well-formed contexts. -/
def decidableModuleValidWf {K : ModuleCheckers} (hS : K.Sound) (hC : K.CompleteWf)
    (m : Module) : Decidable (ModuleValid m) :=
  decidable_of_iff _ (checkModule?_isSome_iff_wf (m := m) hS hC)

end Silmaril.Wasm.Validation
