module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Inst
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.InstPhase
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.SpecGlobals.Defs
public import Silmaril.Proofs.Wasm.Game.Linking.SharedExists
public import Silmaril.Proofs.Wasm.Game.Linking.SpecSetup
public import Silmaril.Wasm.Game.DivAdequacy.Thms

/-!
# The spec stores of a linking setup embed its single-allocation stores

For a linking setup `S` (globals allowed), the provider, the consumer against host stubs and
the linked module prepared by the specification (`Setup.SpecStores`) have stores into which the
setup's `instantiateOnce?` stores embed along injective global maps (`specStores_emb`): the
second copies that `$allocmodule` makes are the setup's globals, the `$evalglobals` copies are
unreachable. The consumer is prepared into the stubbed spec provider store, which embeds the
stubbed provider store of the setup (`Emb.stubOut`). Spec preparation succeeds whenever the
setup's instantiations do (`specStores_nonempty`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.Linking Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC

variable {H : Type}

/-- Every store embeds into itself. -/
theorem Emb.refl (s : Store H) : Emb id Univ s s where
  globals _ _ := rfl
  inj _ _ _ _ e := e
  funcs := by
    have e : function (H := H) id = id := funext fun fi => by
      simp only [function, moduleView_id, id_eq]
    rw [e, List.map_id]
  fdom _ _ := modDom_univ _
  tags := rfl
  mems := rfl
  tables := rfl
  datas := rfl
  elems := rfl
  structs := rfl
  arrays := rfl
  exns := rfl

theorem stubOut_mem {b : Nat} {st : List Nat} {s : Store Nat} {fi : FuncInst Nat}
    (h : fi ∈ (stubOut b st s).funcs) : ∃ g ∈ s.funcs, g.module = fi.module := by
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 h
  simp only [stubOut, List.getElem?_mapIdx] at ha
  cases hg : s.funcs[a]? with
  | none => simp only [hg, Option.map_none, reduceCtorEq] at ha
  | some g =>
    simp only [hg, Option.map_some, Option.some.injEq] at ha
    refine ⟨g, List.mem_of_getElem? hg, ?_⟩
    rw [← ha]
    split <;> rfl

/-- Stubbing functions commutes with embeddings. -/
theorem Emb.stubOut {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store Nat} (h : Emb ρ D s t)
    (b : Nat) (st : List Nat) : Emb ρ D (stubOut b st s) (stubOut b st t) where
  globals := h.globals
  inj := h.inj
  funcs := by
    apply List.ext_getElem?
    intro a
    simp only [Linking.stubOut, List.getElem?_mapIdx, List.getElem?_map, h.funcs]
    cases s.funcs[a]? with
    | none => rfl
    | some fi =>
      simp only [Option.map_some, Option.some.injEq]
      split <;> rfl
  fdom fi hf := by
    obtain ⟨g, hg, he⟩ := stubOut_mem hf
    exact he ▸ h.fdom g hg
  tags := h.tags
  mems := h.mems
  tables := h.tables
  datas := h.datas
  elems := h.elems
  structs := h.structs
  arrays := h.arrays
  exns := h.exns

/-- Typing of non-global external addresses transports through embeddings. -/
theorem Emb.externAddrOk {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store Nat} (h : Emb ρ D s t)
    {xa : ExternAddr} {xt : CExternType} (hx : ExternAddrOk s xa xt)
    (hng : ∀ a, xa ≠ .global a) : ExternAddrOk t xa xt := by
  induction hx with
  | tag hl => exact .tag (h.tags ▸ hl)
  | global _ => exact absurd rfl (hng _)
  | mem hl => exact .mem (h.mems ▸ hl)
  | table hl => exact .table (h.tables ▸ hl)
  | func hl => exact .func (fi := function ρ _) (h.func_lookup hl)
  | sub _ hok hs ih => exact .sub (ih hng) hok hs

/-- Function exports are unchanged by renaming global addresses. -/
theorem exportFuncAddrs_moduleView (ρ : Nat → Nat) (m : ModuleInst) :
    exportFuncAddrs (moduleView ρ m) = exportFuncAddrs m := by
  simp only [exportFuncAddrs, moduleView, List.filterMap_map]
  refine List.filterMap_congr fun e _ => ?_
  simp only [Function.comp_apply]
  cases e.addr <;> rfl

theorem imports_globals (as : List Nat) : ExternAddr.globals (Preparation.imports as) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih => exact ih

theorem imports_not_global {as : List Nat} {xa : ExternAddr} (h : xa ∈ Preparation.imports as) :
    ∀ a, xa ≠ .global a := by
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 h
  intro a e
  cases e

theorem forall₂_emb {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store Nat} (h : Emb ρ D s t)
    {xas : List ExternAddr} {xts : List CExternType} (hx : List.Forall₂ (ExternAddrOk s) xas xts)
    (hng : ∀ xa ∈ xas, ∀ a, xa ≠ .global a) : List.Forall₂ (ExternAddrOk t) xas xts := by
  induction hx with
  | nil => exact .nil
  | cons hh _ ih =>
    exact .cons (h.externAddrOk hh (hng _ List.mem_cons_self))
      (ih fun xa hm => hng xa (List.mem_cons_of_mem _ hm))

theorem withStart_store (c : Config Nat) (st : Option FuncIdx) : (c.withStart st).store = c.store := by
  cases st <;> rfl

/-- The thread of a spec configuration with no code is the renamed thread of the once
configuration, start call included. -/
theorem configThread_withStart {ι : Nat → Nat} {c : Config Nat} {s' : Store Nat} {f' : Frame}
    (hframe : c.frame = frame ι f') (hcode : c.code = []) (st : Option FuncIdx) :
    configThread (c.withStart st) = thread ι (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) := by
  cases st with
  | none => simp only [Config.withStart, configThread, thread, hframe, hcode, admins_nil]
  | some x =>
    simp only [Config.withStart, configThread, thread, hframe, hcode, List.nil_append, admins_cons,
      admin, admins_nil]

/-- The strategy with instantiation phase of a spec configuration with no code is the one of the
once store, running the start call from the once frame. -/
theorem specStrategy_emb (I : ScalarInstance) (P : Silmaril.Wasm.Numerics.Profile)
    {ι : Nat → Nat} (hinj : Function.Injective ι) {c : Config Nat} {s' : Store Nat} {f' : Frame}
    (he : Emb ι Univ s' c.store) (hframe : c.frame = frame ι f') (hcode : c.code = [])
    (st : Option FuncIdx) :
    I.specStrategy P (c.withStart st) =
      I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) := by
  have hth := configThread_withStart (s' := s') hframe hcode st
  show I.instStrategyT P (c.withStart st).store (configThread (c.withStart st)) = _
  rw [hth, withStart_store]
  exact (instStrategyT_emb I P hinj he _).symm

/-- Spec preparation and single allocation give the same strategies (one module). -/
theorem prepare_strategy_eq_once {s s' : Store Nat} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f) (hxg : ExternAddr.globals xas = [])
    (hseg : m.data = [] ∧ m.elems = []) (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧ c.code = [] ∧
      exportFuncAddrs c.frame.module = exportFuncAddrs f'.module ∧
      ∀ (I : ScalarInstance) (P : Silmaril.Wasm.Numerics.Profile),
        I.dstrategy P c.store = I.dstrategy P s' ∧ I.strategy P c.store = I.strategy P s' ∧
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) := by
  obtain ⟨c, ι, hp, hcode, hinj, he, hframe, -, -⟩ :=
    prepare_once (Emb.refl s) Function.injective_id (modDom_of_storeOk hs hw) hxg hseg ho
  have hx : exportFuncAddrs c.frame.module = exportFuncAddrs f'.module := by
    rw [hframe]
    exact exportFuncAddrs_moduleView ι f'.module
  refine ⟨c, hp, hcode, hx, fun I P => ?_⟩
  have hd : I.dstrategy P c.store = I.dstrategy P s' := (dstrategy_emb I P hinj he).symm
  have hp : I.strategy P c.store = I.strategy P s' := by
    rw [← ScalarInstance.forget_dstrategy, ← ScalarInstance.forget_dstrategy, hd]
  exact ⟨hd, hp, specStrategy_emb I P hinj he hframe hcode st⟩

namespace SetupSpec

variable (S : Setup)

theorem provider_segs : S.provider.data = [] ∧ S.provider.elems = [] := by
  obtain ⟨-, -, -, hd, he, -⟩ := profile_sections' S.assembly.providerProfile
  exact ⟨hd, he⟩

theorem consumer_segs : S.consumer.data = [] ∧ S.consumer.elems = [] := by
  obtain ⟨-, -, -, hd, he, -⟩ := profile_sections' S.assembly.consumerProfile
  exact ⟨hd, he⟩

theorem linked_segs : S.linked.data = [] ∧ S.linked.elems = [] := by
  have hout := S.assembly.output
  exact ⟨by rw [hout], by rw [hout]⟩

theorem base_bounded : ∀ fi ∈ S.base.funcs, ModDom (· < S.base.globals.length) fi.module :=
  modDom_of_storeOk S.baseOk S.baseHostFree

/-- The spec preparation of the provider and its embedding. -/
theorem provider_spec : ∃ (c : Config Nat) (ι : Nat → Nat),
    prepare? evalConst? S.base S.provider (Preparation.imports []) = some (c, none) ∧
      Function.Injective ι ∧ Emb ι Univ S.sp c.store ∧ c.frame = frame ι S.fp ∧ c.code = [] ∧
      ∀ fi ∈ S.sp.funcs, ModDom (· < S.sp.globals.length) fi.module := by
  obtain ⟨c, ι, hp, hc, hinj, he, hf, -, hb⟩ := prepare_once (Emb.refl S.base)
    Function.injective_id (base_bounded S) (imports_globals []) (provider_segs S) S.provInst
  exact ⟨c, ι, hp, hinj, he, hf, hc, hb⟩

/-- The spec preparation of the linked module and its embedding. -/
theorem linked_spec : ∃ (c : Config Nat) (ι : Nat → Nat),
    prepare? evalConst? S.base S.linked (Preparation.imports []) = some (c, none) ∧
      Function.Injective ι ∧ Emb ι Univ S.sl c.store ∧ c.frame = frame ι S.fl ∧ c.code = [] := by
  obtain ⟨c, ι, hp, hc, hinj, he, hf, -, -⟩ := prepare_once (Emb.refl S.base)
    Function.injective_id (base_bounded S) (imports_globals []) (linked_segs S) S.linkedInst
  exact ⟨c, ι, hp, hinj, he, hf, hc⟩

/-- The spec preparation of the consumer against host stubs, over any spec provider store into
which the setup's provider store embeds. -/
theorem consumer_spec {ιp : Nat → Nat} {tp : Store Nat} (hinjp : Function.Injective ιp)
    (hep : Emb ιp Univ S.sp tp)
    (hbp : ∀ fi ∈ S.sp.funcs, ModDom (· < S.sp.globals.length) fi.module) :
    ∃ (c : Config Nat) (ι : Nat → Nat),
      prepare? evalConst? (stubOut S.base.funcs.length S.stubs tp) S.consumer
        (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat))) =
          some (c, none) ∧
      Function.Injective ι ∧ Emb ι Univ S.scs c.store ∧ c.frame = frame ι S.fcs ∧ c.code = [] := by
  have hb : ∀ fi ∈ (stubOut S.base.funcs.length S.stubs S.sp).funcs,
      ModDom (· < (stubOut S.base.funcs.length S.stubs S.sp).globals.length) fi.module := by
    intro fi hf
    obtain ⟨g, hg, he⟩ := stubOut_mem hf
    exact he ▸ hbp g hg
  obtain ⟨c, ι, hp, hc, hinj, he, hf, -, -⟩ := prepare_once
    (hep.stubOut S.base.funcs.length S.stubs) hinjp hb (imports_globals _) (consumer_segs S)
    S.stubInst
  exact ⟨c, ι, hp, hinj, he, hf, hc⟩

/-- **Spec preparation succeeds** for every linking setup. -/
theorem specStores_nonempty : Nonempty S.SpecStores := by
  obtain ⟨cp, ιp, hp, hinjp, hep, -, -, hbp⟩ := provider_spec S
  obtain ⟨cl, -, hl, -⟩ := linked_spec S
  obtain ⟨ccs, -, hc, -⟩ := consumer_spec S hinjp hep hbp
  exact ⟨⟨cp, ccs, cl, hp, hc, hl⟩⟩

variable {S}

theorem some_fst_eq {c c' : Config Nat} {st : Option FuncIdx} {x : Option (Config Nat × Option FuncIdx)}
    (h : x = some (c, st)) (h' : x = some (c', st)) : c = c' := by
  have e : some (c, st) = some (c', st) := h.symm.trans h'
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at e
  exact e

/-- The spec store, frame and (empty) code of a configuration over a single-allocation store
and frame. -/
def SpecOf (s : Store Nat) (f : Frame) (c : Config Nat) : Prop :=
  ∃ ι : Nat → Nat, Function.Injective ι ∧ Emb ι Univ s c.store ∧ c.frame = frame ι f ∧ c.code = []

/-- **The spec stores embed the setup's stores** along injective global maps. -/
theorem specStores_emb (X : S.SpecStores) :
    SpecOf S.sp S.fp X.cp ∧ SpecOf S.scs S.fcs X.ccs ∧ SpecOf S.sl S.fl X.cl := by
  obtain ⟨cp, ιp, hp, hinjp, hep, hfp, hcp, hbp⟩ := provider_spec S
  have hXp : cp = X.cp := some_fst_eq hp X.prov
  have hep' : Emb ιp Univ S.sp X.cp.store := hXp ▸ hep
  obtain ⟨ccs, ιc, hc, hinjc, hec, hfc, hcc⟩ := consumer_spec S hinjp hep' hbp
  have hXc : ccs = X.ccs := some_fst_eq hc X.cons
  obtain ⟨cl, ιl, hl, hinjl, hel, hfl, hcl⟩ := linked_spec S
  have hXl : cl = X.cl := some_fst_eq hl X.linked
  refine ⟨⟨ιp, hinjp, hep', hXp ▸ hfp, hXp ▸ hcp⟩, ⟨ιc, hinjc, hXc ▸ hec, hXc ▸ hfc, hXc ▸ hcc⟩,
    ⟨ιl, hinjl, hXl ▸ hel, hXl ▸ hfl, hXl ▸ hcl⟩⟩

theorem provider_dstrategy (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile) :
    S.providerI.dstrategy P X.cp.store = S.providerI.dstrategy P S.sp := by
  obtain ⟨⟨ι, hinj, he, -, -⟩, -, -⟩ := specStores_emb X
  exact (dstrategy_emb S.providerI P hinj he).symm

theorem consumer_dstrategy (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile) :
    S.consumerI.dstrategy P X.ccs.store = S.consumerI.dstrategy P S.scs := by
  obtain ⟨-, ⟨ι, hinj, he, -, -⟩, -⟩ := specStores_emb X
  exact (dstrategy_emb S.consumerI P hinj he).symm

theorem linked_dstrategy (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile) :
    S.linkedI.dstrategy P X.cl.store = S.linkedI.dstrategy P S.sl := by
  obtain ⟨-, -, ⟨ι, hinj, he, -, -⟩⟩ := specStores_emb X
  exact (dstrategy_emb S.linkedI P hinj he).symm

theorem provider_specStrategy (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile) :
    S.providerI.specStrategy P X.cp = S.providerI.instStrategyT P S.sp (configThread ⟨S.sp, S.fp, []⟩) := by
  obtain ⟨⟨ι, hinj, he, hf, hc⟩, -, -⟩ := specStores_emb X
  exact specStrategy_emb S.providerI P hinj he hf hc none

theorem consumer_specStrategy (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile) :
    S.consumerI.specStrategy P X.ccs =
      S.consumerI.instStrategyT P S.scs (configThread ⟨S.scs, S.fcs, []⟩) := by
  obtain ⟨-, ⟨ι, hinj, he, hf, hc⟩, -⟩ := specStores_emb X
  exact specStrategy_emb S.consumerI P hinj he hf hc none

theorem linked_specStrategy (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile) :
    S.linkedI.specStrategy P X.cl = S.linkedI.instStrategyT P S.sl (configThread ⟨S.sl, S.fl, []⟩) := by
  obtain ⟨-, -, ⟨ι, hinj, he, hf, hc⟩⟩ := specStores_emb X
  exact specStrategy_emb S.linkedI P hinj he hf hc none

/-- **The spec stores are the specification's instantiations**, for every profile and host. -/
theorem specStores_instantiate (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics Nat) :
    Instantiate P host S.base S.provider (Preparation.imports []) X.cp ∧
    Instantiate P host (stubOut S.base.funcs.length S.stubs X.cp.store) S.consumer
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      X.ccs ∧
    Instantiate P host S.base S.linked (Preparation.imports []) X.cl := by
  have hpi : S.assembly.providerType.imports = [] := by
    have h := Recipe.validation_imports_length S.assembly.providerValidation
    rw [S.assembly.providerImports] at h
    exact List.length_eq_zero_iff.mp h
  have hvp : ∃ xtE xtI, ModuleOk S.provider ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk S.base) (Preparation.imports []) xtI :=
    ⟨S.assembly.providerType.exports, S.assembly.providerType.imports,
      validate?_sound S.assembly.providerValidation, by rw [hpi]; exact .nil⟩
  obtain ⟨⟨ιp, -, hep, -, -⟩, -, -⟩ := specStores_emb X
  have hxc : List.Forall₂ (ExternAddrOk (stubOut S.base.funcs.length S.stubs X.cp.store))
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      S.assembly.consumerType.imports :=
    (forall₂_emb hep (consumer_imports_ok S.assembly S.provInst) fun _ hm =>
      imports_not_global hm).imp fun _ _ hx => Linking.externAddrOk_stubOut hx
  obtain ⟨mt, hmt⟩ := link?_validate S.link
  have hli : mt.imports = [] := by
    have h := Recipe.validation_imports_length hmt
    rw [S.assembly.output] at h
    exact List.length_eq_zero_iff.mp h
  have hvl : ∃ xtE xtI, ModuleOk S.linked ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk S.base) (Preparation.imports []) xtI :=
    ⟨mt.exports, mt.imports, validate?_sound hmt, by rw [hli]; exact .nil⟩
  exact ⟨(prepare?_sound evalConst?_evalSound X.prov hvp).2,
    (prepare?_sound evalConst?_evalSound X.cons
      ⟨_, _, validate?_sound S.assembly.consumerValidation, hxc⟩).2,
    (prepare?_sound evalConst?_evalSound X.linked hvl).2⟩

end SetupSpec

end Silmaril.Proofs.Wasm.Game.SpecGlobals
