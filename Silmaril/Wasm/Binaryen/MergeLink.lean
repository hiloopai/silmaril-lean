module

public import Silmaril.Wasm.Binaryen.MergeChain

@[expose] public section

/-! # One step of an N-ary merge

For `link? ns P C = some R` with `P` import-free:

* `merged_exists`: if the provider and then the consumer (importing the provider's
  exports) instantiate, so does the linked module (the initializer run is the
  provider's followed by the relocated consumer's, as in
  `OrdinaryInitializers.separate_linked_blocks`; allocation succeeds for any valid
  module, `allocModule_exists`);
* `link_chain`: the separately instantiated store and the linked store are joined
  by a chain (a global-address renaming followed by the linking relation,
  `OrdinaryStoreRelation.separate_linked`).
-/

namespace Silmaril.Wasm.Binaryen.MergeChain

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.Preparation
open Silmaril.Wasm.Binaryen.MergeUntyped

variable {H : Type}

/-! ## Allocation succeeds for valid modules -/

theorem mapM_of_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ (fun a b => f a = some b) l l' → l.mapM f = some l'
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.mapM_cons, Option.bind_eq_bind, h, Option.bind_some, mapM_of_forall₂ t,
      Option.pure_def]

theorem mapM_exists {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := mapM_exists (l := l) (fun x hx => h x (by simp [hx]))
    exact ⟨b :: l', by simp only [List.mapM_cons, Option.bind_eq_bind, hb, Option.bind_some, hl',
      Option.pure_def]⟩

theorem funcs_length_le : ∀ (l : List CExternType), (CExternType.funcs l).length ≤ l.length
  | [] => by simp [CExternType.funcs]
  | x :: l => by
    have := funcs_length_le l
    cases x <;> simp [CExternType.funcs] <;> omega

/-- Every import of a profile module is a function import. -/
theorem profile_imports {m : Module} (hm : Link.GC.inProfile m = true) :
    ∀ i ∈ m.imports, ∃ x, i.type = .func x := by
  simp only [Link.GC.inProfile, Bool.and_eq_true, List.all_eq_true] at hm
  intro i hi
  have h := hm.2 i hi
  revert h
  cases i.type <;> simp

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], .nil, b, hb => by simp at hb
  | a :: _, _ :: _, .cons h t, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, by simp, h⟩
    · obtain ⟨x, hx, hr⟩ := forall₂_mem_right t b hb
      exact ⟨x, by simp [hx], hr⟩

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | [], [], .nil, a, ha => by simp at ha
  | _ :: _, b :: _, .cons h t, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, by simp, h⟩
    · obtain ⟨x, hx, hr⟩ := forall₂_mem_left t a ha
      exact ⟨x, by simp [hx], hr⟩

theorem import_types_funcs {m : Module} {dts : List DefType} {xtI : List CExternType}
    (hm : Link.GC.inProfile m = true)
    (himports : List.Forall₂ (ImportOk { types := dts }) m.imports xtI) :
    ∀ xt ∈ xtI, ∃ d, xt = .func d := by
  intro xt hxt
  obtain ⟨i, hi, hrel⟩ := forall₂_mem_right himports xt hxt
  obtain ⟨x, hx⟩ := profile_imports hm i hi
  obtain ⟨hclose, -⟩ := hrel
  rw [hx] at hclose
  simp only [Context.closeExtern?, Option.map_eq_some_iff] at hclose
  obtain ⟨d, -, rfl⟩ := hclose
  exact ⟨d, rfl⟩

theorem externs_of_funcs : ∀ {l : List CExternType}, (∀ xt ∈ l, ∃ d, xt = .func d) →
    CExternType.globals l = [] ∧ CExternType.tags l = [] ∧ CExternType.mems l = [] ∧
      CExternType.tables l = [] ∧ (CExternType.funcs l).length = l.length
  | [], _ => by
    simp [CExternType.globals, CExternType.tags, CExternType.mems, CExternType.tables,
      CExternType.funcs]
  | x :: l, h => by
    obtain ⟨d, rfl⟩ := h x (by simp)
    have ih := externs_of_funcs (l := l) (fun y hy => h y (by simp [hy]))
    simp [CExternType.globals, CExternType.tags, CExternType.mems, CExternType.tables,
      CExternType.funcs, ih]

/-- **Allocation succeeds** for a valid profile module given as many function
addresses as imports and as many values as globals. -/
theorem allocModule_exists {s : Store H} {m : Module} {as : List Nat} {vals : List Val}
    {xtI xtE : List CExternType} (hm : Link.GC.inProfile m = true)
    (hok : ModuleOk m ⟨xtI, xtE⟩) (hlen : as.length = m.imports.length)
    (hvals : vals.length = m.globals.length) :
    ∃ s' mi, allocModule? s m (imports as) vals [] [] = some (s', mi) := by
  obtain ⟨hmem, htab, htag, hdat, hel, -⟩ := profile_sections hm
  cases hok with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports
      hdisjoint =>
  rename_i dts jts gts tts fdts rts C' C
  subst hC hC'
  have hdts : allocTypes m.types = dts := allocTypes_eq htypes
  obtain ⟨hglob, htagI, hmemI, htabI, hfunI⟩ := externs_of_funcs (import_types_funcs hm himports)
  have hI := himports.length_eq
  have hfl := hfuncs.length_eq
  have hgl := GlobalsOk.length_eq hglobals
  rw [htag] at htags
  cases htags
  rw [htab] at htables
  cases htables
  have ht : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some [] := by rw [htag]; rfl
  have hf : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some fdts := by
    apply mapM_of_forall₂
    rw [hdts]
    exact hfuncs.imp fun fn d hfd => by cases hfd with | mk hd _ _ _ => exact hd
  obtain ⟨xi, hxe⟩ : ∃ xi, m.exports.mapM (allocExport?
      { tags := ExternAddr.tags (imports as) ++ List.range' s.tags.length ([] : List DefType).length,
        globals := ExternAddr.globals (imports as) ++ List.range' s.globals.length
          (min m.globals.length vals.length),
        mems := ExternAddr.mems (imports as) ++ List.range' s.mems.length m.memories.length,
        tables := ExternAddr.tables (imports as) ++ List.range' s.tables.length
          (min m.tables.length ([] : List Ref).length),
        funcs := ExternAddr.funcs (imports as) ++
          (List.range m.funcs.length).map (s.funcs.length + ·) }) = some xi := by
    apply mapM_exists
    intro e he
    obtain ⟨xt, -, hxt⟩ := forall₂_mem_left hexports e he
    change ExternIdxOk _ e.index xt at hxt
    unfold allocExport?
    obtain ⟨ix, hix⟩ : ∃ ix, e.index = ix := ⟨_, rfl⟩
    rw [hix] at hxt ⊢
    apply Option.isSome_iff_exists.mp
    cases hxt with
    | @func x d h =>
      have hb := lt_of_lookup h
      simp only [List.length_append] at hb
      have hb' := funcs_length_le xtI
      have hlt : x.toNat < (ExternAddr.funcs (imports as) ++
          (List.range m.funcs.length).map (s.funcs.length + ·)).length := by
        simp only [imports_funcs, List.length_append, List.length_map, List.length_range]
        omega
      show (Option.map _ ((ExternAddr.funcs (imports as) ++
        (List.range m.funcs.length).map (s.funcs.length + ·))[x.toNat]?.map
          ExternAddr.func)).isSome = true
      rw [List.getElem?_eq_getElem hlt]
      rfl
    | @global x g h =>
      have hb := lt_of_lookup h
      simp only [hglob, List.nil_append] at hb
      have hlt : x.toNat < (ExternAddr.globals (imports as) ++ List.range' s.globals.length
          (min m.globals.length vals.length)).length := by
        simp only [imports_globals, List.nil_append, List.length_range', hvals, Nat.min_self]
        omega
      show (Option.map _ ((ExternAddr.globals (imports as) ++ List.range' s.globals.length
        (min m.globals.length vals.length))[x.toNat]?.map ExternAddr.global)).isSome = true
      rw [List.getElem?_eq_getElem hlt]
      rfl
    | tag h =>
      simp only [htagI, List.nil_append, List.getElem?_nil, reduceCtorEq] at h
    | mem h =>
      simp only [hmemI, hmem, List.nil_append, List.getElem?_nil, reduceCtorEq] at h
    | table h =>
      simp only [htabI, List.nil_append, List.getElem?_nil, reduceCtorEq] at h
  exact ⟨_, _, allocModule?_of ht hf hxe rfl⟩

/-! ## The linked module instantiates when its parts do -/

theorem result_profile {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) : Link.GC.inProfile result = true := by
  rw [w.output]
  rfl

theorem result_imports {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) : result.imports = [] := by
  rw [w.output]

/-- The linked initializer run is the provider's followed by the relocated
consumer's (`OrdinaryInitializers.separate_linked_blocks`, without its linked run). -/
theorem merged_run {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result)
    (hl : link? ns provider consumer = some result) {s : Store H} {cp cc : Config H}
    {startP startC : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (cc, startC)) :
    ∃ sL fL values,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s result (imports [])⟩
        (Module.closedGlobalTypes result) (result.globals.map Global.init) =
          some (sL, fL, values) ∧ values.length = result.globals.length := by
  obtain ⟨sP, fP, valuesP, _, globalsP, allocationP, bindingsP⟩ :=
    prepare?_gc_bindings w.providerProfile hp
  obtain ⟨sC, fC, valuesC, _, globalsC, allocationC, bindingsC⟩ :=
    prepare?_gc_bindings w.consumerProfile hc
  have viewsP := OrdinaryInitializers.provider_initial_views w hl s
  have relatedP : VisibleInitializers.Related Recipe.identity s s
      ⟨[], ModuleInst.initial s provider (imports [])⟩
      ⟨[], ModuleInst.initial s result (imports [])⟩ :=
    VisibleInitializers.Related.of_empty_globals viewsP rfl rfl rfl
  have rewriteP := Initializers.initializer_rewrite w.providerGlobalsRewrite
  rw [Identity.provider_globals w] at rewriteP
  obtain ⟨targetP, frameP, runP, dataP, _, _⟩ :=
    VisibleInitializers.globals_transport relatedP (VisibleInitializers.Bounded.empty rfl)
      (by simp only [ModuleInst.initial, imports_globals, Recipe.identity,
        List.length_nil, Nat.zero_add]) rewriteP globalsP
  have shapeP := (evalGlobals?_shape runP).2.2
  have viewsC := OrdinaryInitializers.consumer_initial_views w hl s cp.store
    bindingsP.function_count
  have viewsC' : Views.Successful (Recipe.relocation provider w.imports)
      (ModuleInst.initial cp.store consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))) frameP.module := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y a rewrite lookup
      rw [shapeP]
      exact viewsC.functions rewrite lookup
    · intro x y a rewrite lookup
      simp only [ModuleInst.initial, imports_globals, List.getElem?_nil, reduceCtorEq] at lookup
    · intro x y d rewrite lookup
      rw [shapeP]
      exact viewsC.types rewrite lookup
  have heapsP := OrdinaryInitializers.allocation_heaps allocationP
  have relatedC : VisibleInitializers.Related (Recipe.relocation provider w.imports)
      cp.store targetP
      ⟨[], ModuleInst.initial cp.store consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))⟩ frameP :=
    VisibleInitializers.Related.of_empty_globals viewsC' (imports_globals _)
      (heapsP.1.trans dataP.structs) (heapsP.2.trans dataP.arrays)
  have lengthC : frameP.module.globals.length =
      (Recipe.relocation provider w.imports).globals +
        (ModuleInst.initial cp.store consumer
          (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).globals.length := by
    rw [shapeP]
    simp only [ModuleInst.initial, imports_globals, Recipe.relocation, List.nil_append,
      List.length_map, List.length_range, Module.closedGlobalTypes, List.length_nil,
      Nat.add_zero]
  obtain ⟨targetC, frameC, runC, dataC, _, _⟩ :=
    VisibleInitializers.globals_transport relatedC
      (VisibleInitializers.Bounded.empty (imports_globals _)) lengthC
      (Initializers.initializer_rewrite w.globalsRewrite) globalsC
  have initializers : result.globals.map Global.init =
      provider.globals.map Global.init ++ w.globals.map Global.init := by
    have globals : result.globals = w.providerGlobals ++ w.globals :=
      congrArg Module.globals w.output
    rw [globals, Identity.provider_globals w, List.map_append]
  refine ⟨targetC, frameC, valuesP ++ valuesC, ?_, ?_⟩
  · rw [Initializers.link_closed_global_types w hl, initializers]
    exact Initializers.globals_append runP runC
  · have globals : result.globals = w.providerGlobals ++ w.globals :=
      congrArg Module.globals w.output
    rw [globals, List.length_append, List.length_append, bindingsP.values_length,
      bindingsC.values_length, w.providerGlobals_length, w.globals_length]

/-- **The linked module instantiates** whenever the provider, and then the consumer
against the provider's exports, do. -/
theorem merged_exists {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result)
    (hl : link? ns provider consumer = some result) {s : Store H} {cp cc : Config H}
    {startP startC : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (cc, startC)) :
    ∃ sl mi, prepare? evalConst? s result (imports []) = some (⟨sl, { module := mi }, []⟩, none) := by
  obtain ⟨sL, fL, values, hrun, hlen⟩ := merged_run w hl hp hc
  obtain ⟨mt, hmt⟩ := link?_valid hl
  obtain ⟨xtI, xtE⟩ := mt
  have hxtI : xtI = [] := by
    cases hmt with
    | mk _ himports _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [result_imports w] at himports
      cases himports
      rfl
  subst hxtI
  obtain ⟨sl, mi, halloc⟩ := allocModule_exists (s := sL) (as := []) (result_profile w) hmt
    (by simp [result_imports w]) hlen
  exact ⟨sl, mi, prepare_of (result_profile w) hrun halloc⟩

theorem storeOk_empty : StoreOk ({} : Store H) := by
  constructor <;> intro x hx <;> cases hx

/-- **One link step is a chain**: from the consumer instantiated after the
provider to the linked module instantiated alone. -/
theorem link_chain {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result)
    (hl : link? ns provider consumer = some result) {cp cc cl : Config H}
    {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? ({} : Store H) provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => ({} : Store H).funcs.length+f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? ({} : Store H) result (imports []) = some (cl, startL))
    (okc : StoreOk cc.store) : Chain cc.store cl.store := by
  obtain ⟨renamed, related⟩ := OrdinaryStoreRelation.separate_linked w hl storeOk_empty hp hc hm
  have cP := (prepared_counts w.providerProfile hp).2
  have cC := (prepared_counts w.consumerProfile hc).2
  have cL := (prepared_counts (result_profile w) hm).2
  have hRg : result.globals.length = provider.globals.length + consumer.globals.length := by
    have globals : result.globals = w.providerGlobals ++ w.globals :=
      congrArg Module.globals w.output
    rw [globals, List.length_append, w.providerGlobals_length, w.globals_length]
  have hempty : ({} : Store H).globals.length = 0 := rfl
  refine .cons (.renamed renamed ?_ ?_) (.cons (.related related
    (GlobalRenameTyping.store_ok renamed okc)) (.refl _))
  · intro a ha
    simp only [OrdinaryStoreRelation.permutation, GlobalPermutation.blocks_apply]
    rw [GlobalPermutation.swapBlocks_after]
    simp only [List.length_nil] at *
    omega
  · simp only [OrdinaryStoreRelation.normalize]
    simp only [List.length_nil] at *
    omega

end Silmaril.Wasm.Binaryen.MergeChain
