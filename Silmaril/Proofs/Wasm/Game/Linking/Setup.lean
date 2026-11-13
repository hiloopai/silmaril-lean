module

public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Proofs.Wasm.Game.Linking.Object
public import Silmaril.Proofs.Wasm.Game.Adequacy.Preservation
public import Silmaril.Proofs.Wasm.Game.Instantiate.Basic
public import Silmaril.Proofs.Wasm.Game.Linking.SetupTyping
public import Silmaril.Wasm.Link.StoreRelation

/-!
# The data of a static link: proofs

* `related`: the shared and linked stores are related by silmaril-lean's
  `StoreRelation.separate_linked`.
* `scs_eq_stubOut`: the consumer-with-stubs store is the shared store with the
  stub set stubbed out.
* `provider_never_throws`, `consumer_never_throws`: with no tags in the base
  store, neither side ever answers with an exception.
* `exists_scalar_setup` (nonvacuity): a successful link (imports resolved
  up to closed subtyping, as the pinned public linker does) and successful
  instantiations give a `Setup` in the scalar fragment. The first port
  assumed exact import resolution (`resolveImportsExact?`); that hypothesis
  is gone (`consumer_imports_ok`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC

namespace Linking

namespace Setup

variable (S : Setup)

/-- The shared and linked stores are related by #1936's store relation
(`StoreRelation.separate_linked`). -/
theorem related : StoreRelation.Related S.sc S.sl :=
  StoreRelation.separate_linked S.assembly S.link S.provInst S.sharedInst S.linkedInst

/-- Stubbing out a store whose function list extends `s.funcs` by `new` leaves `new` alone
when every stub lies inside `s.funcs`. -/
private theorem stubOut_funcs_append (base : Nat) (stubs : List Nat) {s s' : Store Nat}
    {new : List (FuncInst Nat)} (hs : s'.funcs = s.funcs ++ new)
    (hlt : ∀ k ∈ stubs, base + k < s.funcs.length) :
    (stubOut base stubs s').funcs = (stubOut base stubs s).funcs ++ new := by
  simp only [stubOut, hs, List.mapIdx_append]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  rw [List.getElem_mapIdx]
  split
  · rename_i h
    have hk : base + (i + s.funcs.length - base) < s.funcs.length := hlt _ h.2
    omega
  · rfl

/-- The consumer with stubs is the shared store with the stub set stubbed out. Route:
instantiation evaluates only constant expressions, which never call functions, so
`instantiateOnce?` commutes with `stubOut` on functions the consumer does not define. -/
theorem scs_eq_stubOut : S.scs = stubOut S.base.funcs.length S.stubs S.sc := by
  have h' : instantiateOnce? (withFuncs (stubOut S.base.funcs.length S.stubs S.sp).funcs S.sp)
      S.consumer (Preparation.imports
        (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat))) =
        some (S.scs, S.fcs, none) := S.stubInst
  obtain ⟨-, ht⟩ := instantiateOnce?_withFuncs _ (by simp [stubOut])
    S.assembly.consumerProfile S.sharedInst h'
  obtain ⟨_, _, hsc⟩ := StoreRelation.once_function_list S.assembly.consumerProfile S.sharedInst
  have hcount : S.sp.funcs.length = S.base.funcs.length + S.provider.funcs.length :=
    (Views.once_counts S.assembly.providerProfile S.provInst).1
  have hlt : ∀ k ∈ S.stubs, S.base.funcs.length + k < S.sp.funcs.length := fun k hk => by
    rw [hcount]
    exact Nat.add_lt_add_left (S.stubs_lt k hk) _
  have hfuncs : (stubOut S.base.funcs.length S.stubs S.sc).funcs =
      (stubOut S.base.funcs.length S.stubs S.sp).funcs ++ S.sc.funcs.drop S.sp.funcs.length := by
    rw [stubOut_funcs_append _ _ hsc hlt, hsc, List.drop_left]
  rw [ht, withFuncs, ← hfuncs]
  rfl

/-- No tags in the fragment, hence no exception: if the base store has no tags and no
exception instances, the provider object never answers `throw a`. -/
theorem provider_never_throws (hS : S.Scalar) (hbase : S.base.tags = [] ∧ S.base.exns = [])
    (P : Profile) {t : List (Ev S.providerI.F)} (ht : t ∈ S.providerI.objPlays P S.sp)
    (f : S.providerI.F.Op) (a : Nat) : (Ev.ans f (.throw a) : Ev S.providerI.F) ∉ t := by
  obtain ⟨p, hp, rfl⟩ := ht
  intro hmem
  have hm : (.inr (.ans f (.throw a)) : Move S.providerI.E S.providerI.F) ∈ p := by
    simp only [upper, List.mem_filterMap] at hmem
    obtain ⟨m, hm, hm'⟩ := hmem
    cases m with
    | inl x => simp [Sum.getRight?] at hm'
    | inr x =>
      simp only [Sum.getRight?, Option.some.injEq] at hm'
      subst hm'
      exact hm
  have stat := StoreRelation.once_static S.assembly.providerProfile S.provInst
  have henv : S.providerI.PlayThrowsBelow 0 p := fun e => Fin.elim0 e.1
  exact ScalarInstance.no_throw_of_no_tags (I := S.providerI) hS.provider
    (stat.tags.symm.trans hbase.1) (stat.exns.symm.trans hbase.2) hp henv f a hm

/-- The consumer with stubs never answers `throw a` when its environment (the provider, by
`provider_never_throws`) never throws. -/
theorem consumer_never_throws (hS : S.Scalar) (hbase : S.base.tags = [] ∧ S.base.exns = [])
    (P : Profile) {p : List (Move S.consumerI.E S.consumerI.F)}
    (hp : p ∈ S.consumerI.plays P S.scs) (henv : S.consumerI.PlayThrowsBelow 0 p)
    (f : S.consumerI.F.Op) (a : Nat) :
    (.inr (.ans f (.throw a)) : Move S.consumerI.E S.consumerI.F) ∉ p := by
  have statP := StoreRelation.once_static S.assembly.providerProfile S.provInst
  have statC := StoreRelation.once_static S.assembly.consumerProfile S.stubInst
  have htags : S.scs.tags = [] := by
    rw [← statC.tags]; exact statP.tags.symm.trans hbase.1
  have hexns : S.scs.exns = [] := by
    rw [← statC.exns]; exact statP.exns.symm.trans hbase.2
  exact ScalarInstance.no_throw_of_no_tags (I := S.consumerI) hS.consumer htags hexns hp henv f a

end Setup

/-! ### Helpers for `exists_scalar_setup` -/

private theorem lookup₂ {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

private theorem forall₂_of_lookup₂ {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (length : xs.length = ys.length)
    (lookup : ∀ (i : Nat) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → R x y) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp length.symm
    subst ys; exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at length; omega
    | cons y ys =>
      refine .cons (lookup 0 x y rfl rfl) (ih (by simpa using length) ?_)
      intro i x' y' hx hy
      exact lookup (i+1) x' y' hx hy

/-- The function-instance map of `stubOut`. -/
private theorem stubOut_lookup (base : Nat) (stubs : List Nat) (s : Store Nat) (a : Nat) :
    (stubOut base stubs s).funcs[a]? = s.funcs[a]?.map fun fi =>
      if base ≤ a ∧ a - base ∈ stubs then { fi with code := .host (stubs.idxOf (a - base)) }
      else fi := by
  simp only [stubOut, List.getElem?_mapIdx]

private def HostFree (s : Store Nat) : Prop := ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f

private theorem HostFree.append {s s' : Store Nat} (h : HostFree s) {new : List (FuncInst Nat)}
    (hs : s'.funcs = s.funcs ++ new) (hnew : ∀ fi ∈ new, ∃ code, fi.code = .wasm code) :
    HostFree s' := by
  intro fi hfi
  rw [hs] at hfi
  rcases List.mem_append.mp hfi with hfi | hfi
  · exact h fi hfi
  · exact hnew fi hfi

private theorem HostFree.no_host {s : Store Nat} (h : HostFree s) {a : Nat} {fi : FuncInst Nat}
    {k : Nat} (hfi : s.funcs[a]? = some fi) (hc : fi.code = .host k) : False := by
  obtain ⟨f, hf⟩ := h fi (List.mem_of_getElem? hfi)
  rw [hf] at hc
  cases hc

/-- Well-formedness from typed export addresses. -/
private theorem wellFormed_of {I : ScalarInstance} {s : Store Nat} (hs : StoreOk s)
    (hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, s.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports)
    (hhost : ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi →
      fi.code = .host h → ∃ hlt : h < I.imports.length,
        Expand fi.type (I.imports.get ⟨h, hlt⟩).toComp) :
    I.WellFormed s where
  storeOk := hs
  addrs_length := hexp.length_eq
  export_type j := by
    have hj : j.1 < I.addrs.length := by rw [hexp.length_eq]; exact j.2
    obtain ⟨ft, hft, fi, hfi, hty⟩ := lookup₂ hexp (List.getElem?_eq_getElem hj)
    have hft' : I.exports.get j = ft := by
      rw [List.get_eq_getElem]
      exact Option.some.inj ((List.getElem?_eq_getElem j.2).symm.trans hft)
    refine ⟨fi, ?_, hft' ▸ FnType.expand_of_ofDefType? hty⟩
    simp only [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
    exact hfi
  host_type := hhost

/-- The canonical stubs are provider functions. -/
private theorem canonicalStubs_lt {ns : String} {provider consumer linked : Module}
    (w : Recipe.Assembly ns provider consumer linked) (base : Nat) (exps : List Nat) :
    ∀ k ∈ canonicalStubs w.imports base provider.funcs.length exps,
      k < provider.funcs.length := by
  intro k hk
  simp only [canonicalStubs, List.mem_dedup, List.mem_append, List.mem_map,
    List.mem_filterMap] at hk
  rcases hk with ⟨f, hf, rfl⟩ | ⟨a, -, hsome⟩
  · exact Resolution.assembly_imports_bounded w f hf
  · split at hsome
    · cases hsome
      omega
    · cases hsome

/-- The stub at address `a` (relative to `b`) has the type listed for it in `stubTypes`. -/
private theorem stub_type {sp : Store Nat} {b : Nat} {stubs : List Nat}
    {stubTypes : List FnType}
    (hstub : List.Forall₂ (fun k ft => ∃ fi : FuncInst Nat, sp.funcs[b + k]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) stubs stubTypes)
    (a : Nat) (h₁ : b ≤ a) (h₂ : a - b ∈ stubs) :
    ∃ (hlt : stubs.idxOf (a - b) < stubTypes.length) (fi : FuncInst Nat),
      sp.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some (stubTypes.get ⟨_, hlt⟩) := by
  have hj : stubs.idxOf (a - b) < stubs.length := List.idxOf_lt_length_of_mem h₂
  have hjv : stubs[stubs.idxOf (a - b)] = a - b := List.getElem_idxOf hj
  obtain ⟨ft, hft, fi, hfi, hty⟩ := lookup₂ hstub (List.getElem?_eq_getElem hj)
  have hlt : stubs.idxOf (a - b) < stubTypes.length := by rw [← hstub.length_eq]; exact hj
  have ha : b + stubs[stubs.idxOf (a - b)] = a := by rw [hjv]; omega
  have hft' : stubTypes.get ⟨_, hlt⟩ = ft := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hft)
  refine ⟨hlt, fi, ?_, ?_⟩
  · rw [← ha]; exact hfi
  · rw [hft']; exact hty

/-- Typing of the stubbed functions of a store, by their position in the stub list. -/
private def StubsTyped (b : Nat) (stubs : List Nat) (stubTypes : List FnType) (s : Store Nat) :
    Prop :=
  ∀ a, b ≤ a → a - b ∈ stubs → ∀ fi, s.funcs[a]? = some fi →
    ∃ hlt : stubs.idxOf (a - b) < stubTypes.length, Expand fi.type (stubTypes.get ⟨_, hlt⟩).toComp

/-- `stubOut` recodes typed stubs as host functions (the function part of `Recoded`). -/
private theorem stubOut_recoded_funcs {b : Nat} {stubs : List Nat} {stubTypes : List FnType}
    {s : Store Nat} (hT : StubsTyped b stubs stubTypes s) :
    List.Forall₂ (fun fi fi' : FuncInst Nat => fi'.type = fi.type ∧ fi'.module = fi.module ∧
      (fi'.code = fi.code ∨ ∃ h, fi'.code = .host h ∧ ∃ ps rs, Expand fi.type (.func ps rs)))
      s.funcs (stubOut b stubs s).funcs := by
  refine forall₂_of_lookup₂ (by simp [stubOut]) fun a fi fi' h₁ h₂ => ?_
  have hfi' : (if b ≤ a ∧ a - b ∈ stubs then { fi with code := .host (stubs.idxOf (a - b)) }
      else fi) = fi' := by
    simpa only [stubOut_lookup, h₁, Option.map_some, Option.some.injEq] using h₂
  rw [← hfi']
  split
  · rename_i hcond
    obtain ⟨hlt, hexp⟩ := hT a hcond.1 hcond.2 fi h₁
    exact ⟨rfl, rfl, .inr ⟨_, rfl, _, _, hexp⟩⟩
  · exact ⟨rfl, rfl, .inl rfl⟩

/-- In a host-free store with typed stubs, every host function of the stubbed-out store is a
stub, typed by `stubTypes`. -/
private theorem stubOut_host_type {b : Nat} {stubs : List Nat} {stubTypes : List FnType}
    {s : Store Nat} (hfree : HostFree s) (hT : StubsTyped b stubs stubTypes s) :
    ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), (stubOut b stubs s).funcs[a]? = some fi →
      fi.code = .host h → ∃ hlt : h < stubTypes.length,
        Expand fi.type (stubTypes.get ⟨h, hlt⟩).toComp := by
  intro a fi h hfi hcode
  obtain ⟨fi₀, h₀, hfi₀⟩ := Option.map_eq_some_iff.mp ((stubOut_lookup b stubs s a).symm.trans hfi)
  by_cases hcond : b ≤ a ∧ a - b ∈ stubs
  · have hfi' : { fi₀ with code := .host (stubs.idxOf (a - b)) } = fi := by
      simpa only [hcond, and_self, ite_true] using hfi₀
    have hh : stubs.idxOf (a - b) = h := by
      simpa only [← hfi', FuncCode.host.injEq] using hcode
    obtain ⟨hlt, hexp⟩ := hT a hcond.1 hcond.2 fi₀ h₀
    exact ⟨hh ▸ hlt, by subst hh; rw [← hfi']; exact hexp⟩
  · have hfi' : fi₀ = fi := by simpa only [hcond, ite_false] using hfi₀
    exact (hfree.no_host h₀ (hfi' ▸ hcode)).elim

/-- **Nonvacuity of `Setup.Scalar`.** A successful static link with successful provider and
linked instantiations over a host-free well-typed base store, and scalar types for the
canonical stub set and the linked exports, yields a `Setup` in the scalar fragment. -/
theorem exists_scalar_setup {ns : String} {provider consumer linked : Module}
    (w : Recipe.Assembly ns provider consumer linked)
    (hl : link? ns provider consumer = some linked) {base : Store Nat}
    (baseHostFree : ∀ fi ∈ base.funcs, ∃ f, fi.code = .wasm f) (baseOk : StoreOk base)
    {sp sl : Store Nat} {fp fl : Frame} {startP startL : Option FuncIdx}
    (hp : instantiateOnce? base provider (Preparation.imports []) = some (sp, fp, startP))
    (hm : instantiateOnce? base linked (Preparation.imports []) = some (sl, fl, startL))
    {stubTypes exportTypes : List FnType}
    (hstub : List.Forall₂
      (fun k ft => ∃ fi : FuncInst Nat, sp.funcs[base.funcs.length + k]? = some fi ∧
        FnType.ofDefType? fi.type = some ft)
      (canonicalStubs w.imports base.funcs.length provider.funcs.length
        (exportFuncAddrs fl.module)) stubTypes)
    (hexp : List.Forall₂
      (fun a ft => ∃ fi : FuncInst Nat, sl.funcs[a]? = some fi ∧
        FnType.ofDefType? fi.type = some ft)
      (exportFuncAddrs fl.module) exportTypes) :
    ∃ S : Setup, S.namespaceName = ns ∧ S.provider = provider ∧ S.consumer = consumer ∧
      S.linked = linked ∧ S.base = base ∧ S.sp = sp ∧ S.sl = sl ∧ S.fl = fl ∧
      S.stubs = canonicalStubs w.imports base.funcs.length provider.funcs.length
        (exportFuncAddrs fl.module) ∧
      S.stubTypes = stubTypes ∧ S.exportTypes = exportTypes ∧ S.Scalar := by
  have hprofileL : inProfile linked = true := by rw [w.output]; rfl
  obtain ⟨_, _, _, _, _, _, hstP⟩ := PreparationOnce.once_allocation w.providerProfile hp
  obtain ⟨_, _, _, _, _, _, hstL⟩ := PreparationOnce.once_allocation hprofileL hm
  have hp' : instantiateOnce? base provider (Preparation.imports []) = some (sp, fp, none) :=
    hstP ▸ hp
  have hm' : instantiateOnce? base linked (Preparation.imports []) = some (sl, fl, none) :=
    hstL ▸ hm
  obtain ⟨sc, fc, hc⟩ := shared_exists w hl hp' hm'
  have hcount : sp.funcs.length = base.funcs.length + provider.funcs.length :=
    (Views.once_counts w.providerProfile hp').1
  generalize hst : canonicalStubs w.imports base.funcs.length provider.funcs.length
    (exportFuncAddrs fl.module) = stubs at hstub ⊢
  obtain ⟨scs, fcs, hcs⟩ := withFuncs_exists w hl hp' hm'
    (stubOut base.funcs.length stubs sp).funcs (by simp [stubOut])
  -- the stub set
  have stubs_nodup : stubs.Nodup := by rw [← hst]; exact List.nodup_dedup _
  have stubs_lt : ∀ k ∈ stubs, k < provider.funcs.length := hst ▸ canonicalStubs_lt w _ _
  have imports_stubbed : ∀ f ∈ w.imports, f.toNat ∈ stubs := by
    intro f hf
    rw [← hst]
    exact List.mem_dedup.mpr (List.mem_append_left _ (List.mem_map_of_mem hf))
  have exports_stubbed : ∀ a ∈ exportFuncAddrs fl.module, base.funcs.length ≤ a →
      a < base.funcs.length + provider.funcs.length → a - base.funcs.length ∈ stubs := by
    intro a ha h₁ h₂
    rw [← hst]
    exact List.mem_dedup.mpr (List.mem_append_right _
      (List.mem_filterMap.mpr ⟨a, ha, ite_eq_left ⟨h₁, h₂⟩⟩))
  -- typing
  obtain ⟨hspOk, newP, hspF, hnewP⟩ :=
    once_storeOk_closed baseOk w.providerValidation w.providerImports hp'
  obtain ⟨mtL, hvL⟩ := link?_validate hl
  obtain ⟨hslOk, newL, hslF, hnewL⟩ :=
    once_storeOk_closed baseOk hvL (by rw [w.output]) hm'
  obtain ⟨hscOk, newC, hscF, hnewC⟩ :=
    once_storeOk hspOk w.consumerValidation (consumer_imports_ok w hp') hc
  have hfP : HostFree sp := HostFree.append baseHostFree hspF hnewP
  have hfC : HostFree sc := HostFree.append hfP hscF hnewC
  have hfL : HostFree sl := HostFree.append baseHostFree hslF hnewL
  have hrel : StoreRelation.Related sc sl := StoreRelation.separate_linked w hl hp' hc hm'
  have hscp : ∀ a, a < sp.funcs.length → sc.funcs[a]? = sp.funcs[a]? := by
    intro a ha
    rw [hscF, List.getElem?_append_left ha]
  -- the stub types
  have hscT : StubsTyped base.funcs.length stubs stubTypes sc := by
    intro a h₁ h₂ fi hfi
    obtain ⟨hlt, fi₁, h₁', hty⟩ := stub_type hstub a h₁ h₂
    have hb : a - base.funcs.length < provider.funcs.length := stubs_lt _ h₂
    have hfi₁ : fi₁ = fi :=
      Option.some.inj (h₁'.symm.trans ((hscp a (by omega)).symm.trans hfi))
    exact ⟨hlt, hfi₁ ▸ FnType.expand_of_ofDefType? hty⟩
  let S : Setup :=
    { namespaceName := ns, provider := provider, consumer := consumer, linked := linked,
      assembly := w, link := hl, base := base, baseHostFree := baseHostFree, baseOk := baseOk,
      sp := sp, sc := sc, scs := scs, sl := sl, fp := fp, fc := fc, fcs := fcs, fl := fl,
      stubs := stubs, stubs_nodup := stubs_nodup, stubs_lt := stubs_lt,
      imports_stubbed := imports_stubbed, exports_stubbed := exports_stubbed,
      stubTypes := stubTypes, exportTypes := exportTypes, provInst := hp', sharedInst := hc,
      stubInst := hcs, linkedInst := hm' }
  have hscs : scs = stubOut base.funcs.length stubs sc := S.scs_eq_stubOut
  refine ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- provider
    show ScalarInstance.WellFormed
      ⟨[], stubTypes, stubs.map (base.funcs.length + ·), sp⟩ sp
    refine wellFormed_of hspOk ?_ (fun a fi h hfi hcode => (hfP.no_host hfi hcode).elim)
    refine forall₂_of_lookup₂ (by simp [hstub.length_eq]) fun i a ft ha hft => ?_
    obtain ⟨k, hk, hak⟩ : ∃ k, stubs[i]? = some k ∧ base.funcs.length + k = a := by
      simpa only [List.getElem?_map, Option.map_eq_some_iff] using ha
    obtain ⟨ft', hft', hR⟩ := lookup₂ hstub hk
    have hft_eq : ft' = ft := Option.some.inj (hft'.symm.trans hft)
    rw [← hak, ← hft_eq]
    exact hR
  · -- consumer with stubs
    show ScalarInstance.WellFormed ⟨stubTypes, exportTypes, exportFuncAddrs fl.module, scs⟩ scs
    rw [hscs]
    refine wellFormed_of (storeOk_recode hscOk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      stubOut_recoded_funcs hscT⟩) ?_ (stubOut_host_type hfC hscT)
    refine hexp.imp fun a ft ⟨fi, hfi, hty⟩ => ?_
    obtain ⟨fi₀, h₀, hf⟩ := hrel.function_lookup_reverse hfi
    refine ⟨_, by rw [stubOut_lookup, h₀]; rfl, ?_⟩
    split <;> (show FnType.ofDefType? fi₀.type = some ft; rw [hf.type_eq]; exact hty)
  · -- shared
    show ScalarInstance.WellFormed ⟨[], exportTypes, exportFuncAddrs fl.module, sc⟩ sc
    refine wellFormed_of hscOk ?_ (fun a fi h hfi hcode => (hfC.no_host hfi hcode).elim)
    refine hexp.imp fun a ft ⟨fi, hfi, hty⟩ => ?_
    obtain ⟨fi₀, h₀, hf⟩ := hrel.function_lookup_reverse hfi
    exact ⟨fi₀, h₀, by rw [hf.type_eq]; exact hty⟩
  · -- linked
    show ScalarInstance.WellFormed ⟨[], exportTypes, exportFuncAddrs fl.module, sl⟩ sl
    exact wellFormed_of hslOk hexp (fun a fi h hfi hcode => (hfL.no_host hfi hcode).elim)

end Linking

end Silmaril.Wasm.Game
