module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLink
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkNames
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Numerics (Profile)

variable {Pf : Profile}

/-! ## The trampolines alone, relocated -/

/-- The trampolines of `ims` alone (import `k` lowering `fid k` in instance `inst`). -/
noncomputable def trampsLStore (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (inst : InstId) (fid : Nat → FuncId) (ims : Iface) :
    Store (CanonHost (core3R P V IR)) :=
  { funcs := trampsL P V IR inst fid ims }

/-- **The shared trampoline store is the trampolines alone relocated past `cs₀`.** -/
theorem reloc_trampsL (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId)
    (fid : Nat → FuncId) (ims : Iface) :
    reloc cs₀ (trampsLStore Pf V IR inst fid ims) = trampStoreL Pf cs₀ inst fid ims := by
  have hf : (trampsL Pf V IR inst fid ims).map (sh cs₀).finst = trampsL Pf V IR inst fid ims := by
    refine List.ext_getElem? fun i => ?_
    simp only [trampsL, List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
    cases ims[i]? <;> rfl
  change Store (CanonHost (core3R Pf V IR)) at cs₀
  simp only [reloc, Store.app, Shift.store, trampsLStore, trampStoreL, List.map_nil,
    List.append_nil, hf]

/-- The trampolines paired with their import index. -/
noncomputable def trampsP (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (inst : InstId) (fid : Nat → FuncId) (ims : Iface) :
    Store (CanonHost (core3R P V IR) × Nat) :=
  { funcs := ims.mapIdx fun k p =>
      ⟨SingleThreaded.ofFlatType (flatV1 p.2), {},
        .host (.lowered (fid k) (witFt p.2) {} inst, k)⟩ }

theorem trampsP_fst (inst : InstId) (fid : Nat → FuncId) (ims : Iface) :
    Store.mapH Prod.fst (trampsP Pf V IR inst fid ims) = trampsLStore Pf V IR inst fid ims := by
  simp only [Store.mapH, trampsP, trampsLStore, trampsL]
  congr 1
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
  cases ims[i]? <;> rfl

theorem trampsP_snd (inst : InstId) (fid : Nat → FuncId) (ims : Iface) :
    Store.mapH Prod.snd (trampsP Pf V IR inst fid ims) = Silmaril.Wasm.Game.importStore (importDefTypes ims) := by
  simp only [Store.mapH, trampsP, Silmaril.Wasm.Game.importStore, importDefTypes]
  congr 1
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
  cases ims[i]? <;> rfl

theorem trampsP_hosts {c : SimpleI} (inst : InstId) (fid : Nat → FuncId) :
    HostsSat (fun h => ∃ (k : Nat) (hk : k < c.imports.length),
      h = (.lowered (fid k) (witFt c.imports[k].2) {} inst, k)) (trampsP Pf V IR inst fid c.imports) := by
  intro a fi h ha hc
  simp only [trampsP, List.getElem?_mapIdx] at ha
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨hk, hpk⟩ := List.getElem?_eq_some_iff.1 hp
  refine ⟨a, hk, ?_⟩
  have hh := FuncCode.host.inj hc
  rw [← hh, hpk]

theorem trampStoreL_getElem? (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId)
    (fid : Nat → FuncId) (ims : Iface) (i : Nat) :
    (trampStoreL Pf cs₀ inst fid ims : Store _).funcs[(cs₀ : Store _).funcs.length + i]? =
      ims[i]?.map fun p => trampFIL Pf V IR inst (fid i) p.2 := by
  simp only [trampStoreL]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  simp only [trampsL, List.getElem?_mapIdx]

theorem trampStoreL_type (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId)
    (fid : Nat → FuncId) (ims : Iface) (i : Nat) (hi : i < (importDefTypes ims).length) :
    ∃ fi, (trampStoreL Pf cs₀ inst fid ims : Store _).funcs[(cs₀ : Store _).funcs.length + i]? =
      some fi ∧ fi.type = (importDefTypes ims)[i] := by
  have hi' : i < ims.length := importDefTypes_length ims ▸ hi
  refine ⟨trampFIL Pf V IR inst (fid i) ims[i].2, ?_, ?_⟩
  · rw [trampStoreL_getElem?, List.getElem?_eq_getElem hi']
    rfl
  · simp only [importDefTypes, List.getElem_map]
    rfl

/-! ## The core facts in the shared store -/

theorem externAddrsOk_trampL {c : SimpleI} (hi : c.Inst) {mt : Validation.CModuleType}
    (hv : Validation.validate? c.mod.mod = some mt)
    (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId) (fid : Nat → FuncId) :
    externAddrsOk? (trampStoreL Pf cs₀ inst fid c.imports)
      ((List.range' (cs₀ : Store _).funcs.length c.imports.length).map ExternAddr.func)
      mt.imports = true := by
  have hmt := inst_importTypes hi hv
  have hok : ∀ d ∈ importDefTypes c.imports, Validation.ExternTypeOk {} (.func d) :=
    fun d hd => Silmaril.Wasm.Component.Engine.Core3.validate?_imports_externTypeOk hv _
      (hmt ▸ List.mem_map_of_mem hd)
  have h := externAddrsOk_range (s := (trampStoreL Pf cs₀ inst fid c.imports : Store _))
    (importDefTypes c.imports) _ hok (trampStoreL_type cs₀ inst fid c.imports)
  rw [importDefTypes_length] at h
  rw [hmt]
  exact h

theorem externTypeE_trampL {c : SimpleI} (hi : c.Inst)
    (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId) (fid : Nat → FuncId)
    (i : Nat) (hi' : i < c.imports.length) :
    ∃ h, Core3.externTypeE? (trampStoreL Pf cs₀ inst fid c.imports)
      (.func ((cs₀ : Store _).funcs.length + i)) =
      some ⟨.func ((importDefTypes c.imports)[i]'(by rw [importDefTypes_length]; exact hi')), h⟩ := by
  obtain ⟨I, ⟨mt, hIs⟩, -⟩ := hi.inst
  have hmt := inst_importTypes hi hIs.valid
  have hil : i < (importDefTypes c.imports).length := by rw [importDefTypes_length]; exact hi'
  have hok : Validation.ExternTypeOk {} (.func ((importDefTypes c.imports)[i]'hil)) :=
    Silmaril.Wasm.Component.Engine.Core3.validate?_imports_externTypeOk hIs.valid _
      (hmt ▸ List.mem_map_of_mem (List.getElem_mem hil))
  have hc : Validation.ExternTypeOk.check {} (.func ((importDefTypes c.imports)[i]'hil)) = true :=
    Validation.ExternTypeOk.check_complete
      (Validation.tyOk_check_complete_all {} Validation.TypeCtx.ok_empty rfl) hok
  obtain ⟨fi, hfi, hty⟩ := trampStoreL_type cs₀ inst fid c.imports i hil
  refine ⟨Validation.ExternTypeOk.check_sound hc, ?_⟩
  simp only [Core3.externTypeE?, externAddrType?, hfi, Option.map_some, hty, hc, dite_true]

/-- **The import vector of the importer's core instantiation in the shared store**: import `i`
of the module is the trampoline at `b + i`, exported by the inline core instance under its
name. -/
theorem coreImportsFor_trampL {c : SimpleI} (hc : c.Good) (hi : c.Inst)
    (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId) (fid : Nat → FuncId)
    (fr : Frame (core3R Pf V IR))
    (hfr : fr.coreInstance? 0 = some (envExportsAt (cs₀ : Store _).funcs.length c.mod.imports)) :
    coreImportsFor? (trampStoreL Pf cs₀ inst fid c.imports) c.mod.mod [("env", 0)] fr =
      some ((List.range' (cs₀ : Store _).funcs.length c.imports.length).map ExternAddr.func) := by
  obtain ⟨hlen, hT⟩ := importTypesE_getElem hi
  have hnd : (c.mod.imports.map (·.1)).Nodup := by
    rw [hc.imports, List.map_map]
    exact hi.importNames
  have hlenm : c.mod.imports.length = c.imports.length := by rw [hc.imports, List.length_map]
  show (Core3.importTypesE c.mod.mod).mapM _ = _
  refine mapM_eq_some_of_getElem
    (by rw [hlen]; exact (Eq.trans (List.length_map _) List.length_range').symm) fun i h₁ => ?_
  have h₂ : i < c.imports.length := hlen ▸ h₁
  obtain ⟨e₁, e₂, e₃⟩ := hT i h₁ h₂
  have hname : c.mod.imports[i].1 = c.imports[i].1 := by
    simp only [hc.imports, List.getElem_map]
  have hlk : lookupExport? (envExportsAt (cs₀ : Store _).funcs.length c.mod.imports)
      c.imports[i].1 = some (.func ((cs₀ : Store _).funcs.length + i)) := by
    have h := lookup_mapIdx_val (·.1) ExternAddr.func (cs₀ : Store _).funcs.length c.mod.imports i
      (hlenm ▸ h₂) hnd
    rw [← hname]
    exact h
  obtain ⟨hτ, hext⟩ := externTypeE_trampL (Pf := Pf) (V := V) (IR := IR) hi cs₀ inst fid i h₂
  have hsub : (core3R Pf V IR).ExternSub ⟨_, hτ⟩ (Core3.importTypesE c.mod.mod)[i].2.2 := by
    show Validation.ExternSub {} _ (Core3.importTypesE c.mod.mod)[i].2.2.val
    rw [e₃]
    exact Validation.ExternSub.refl _ _
  have hget : ((List.range' (cs₀ : Store _).funcs.length c.imports.length).map
      ExternAddr.func)[i]'(by rw [List.length_map, List.length_range']; exact h₂) =
        .func ((cs₀ : Store _).funcs.length + i) := by
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
  refine Eq.trans ?_ (congrArg some hget.symm)
  simp only [coreImportFor?, e₁, e₂, List.lookup_cons, beq_self_eq_true, Option.bind_eq_bind,
    Option.bind_some, hfr]
  have hext' : (core3R Pf V IR).externType? (trampStoreL Pf cs₀ inst fid c.imports)
      (ExternAddr.func ((cs₀ : Store _).funcs.length + i)) = some ⟨_, hτ⟩ := hext
  erw [Option.bind_some, hlk, Option.bind_some, hext', Option.bind_some]
  split
  · rfl
  · contradiction

/-- **The core facts of the importer in the shared store, from `SimpleI.Inst`**, for an importer
module without data and element segments: for any game instance `I` of the module, any core
store `cs₀`, instance `inst` and lowered callees `fid`, there are a store `r` whose host code
pairs trampoline `k` with `k`, whose second projection is `I.store`, and a core instance `ci`
such that the importer's core instantiation in `trampStoreL` gives `reloc cs₀` of the first
projection of `r` (`CoreFactsL`), with export `k` at `addrL b I k = b + I.addrs[k]`. -/
theorem coreFactsL_of_inst {c : SimpleI} (hc : c.Good) (hi : c.Inst)
    (hseg : c.mod.mod.data = [] ∧ c.mod.mod.elems = []) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId)
    (fid : Nat → FuncId) :
    ∃ (r : Store (CanonHost (core3R Pf V IR) × Nat)) (ci : (core3R Pf V IR).Inst),
      Store.mapH Prod.snd r = I.store ∧
      HostsSat (fun h => ∃ (k : Nat) (hk : k < c.imports.length),
        h = (.lowered (fid k) (witFt c.imports[k].2) {} inst, k)) r ∧
      CoreFactsL c cs₀ inst fid (addrL (cs₀ : Store _).funcs.length I)
        (reloc cs₀ (Store.mapH Prod.fst r)) ci := by
  obtain ⟨⟨mt, hIs⟩, -, -⟩ := hI
  have hmt := inst_importTypes hi hIs.valid
  have hlen : mt.imports.length = c.imports.length := by
    rw [hmt, List.length_map, importDefTypes_length]
  have hfuncs : Validation.CExternType.funcs mt.imports = importDefTypes c.imports := by
    rw [hmt, funcs_map_func]
  obtain ⟨f, hf, haddr⟩ := hIs.instantiated
  rw [hfuncs, hlen, ← trampsP_snd (Pf := Pf) (V := V) (IR := IR) inst fid, instantiateOnce?_mapH] at hf
  obtain ⟨r, hr, hrs⟩ := mapS_eq_some hf
  have ho₁ : instantiateOnce? (trampsLStore Pf V IR inst fid c.imports) c.mod.mod
      ((List.range c.imports.length).map ExternAddr.func) = some (Store.mapH Prod.fst r, f, none) := by
    rw [← trampsP_fst (Pf := Pf) (V := V) (IR := IR) inst fid, instantiateOnce?_mapH, hr]
    rfl
  have ho₂ : instantiateOnce? (trampStoreL Pf cs₀ inst fid c.imports : Store _) c.mod.mod
      ((List.range' (cs₀ : Store _).funcs.length c.imports.length).map ExternAddr.func) =
        some (reloc cs₀ (Store.mapH Prod.fst r), (sh cs₀).frame f, none) := by
    have e := range'_eq_map_xa (H := CanonHost (core3R Pf V IR)) cs₀ c.imports.length
    rw [← reloc_trampsL]
    erw [e, instantiateOnce?_reloc _ _ _ _ hseg, ho₁]
    rfl
  have hprep : (core3R Pf V IR).prepare? (trampStoreL Pf cs₀ inst fid c.imports) c.mod.mod
      ((List.range' (cs₀ : Store _).funcs.length c.imports.length).map ExternAddr.func) =
        some (reloc cs₀ (Store.mapH Prod.fst r), ((sh cs₀).frame f).module, none) := by
    show Core3.prepareE? _ _ _ = _
    simp only [Core3.prepareE?, hIs.valid]
    split
    · erw [ho₂]
      rfl
    · exact absurd (externAddrsOk_trampL (Pf := Pf) (V := V) (IR := IR) hi hIs.valid cs₀ inst fid) ‹_›
  have ha : Silmaril.Wasm.Game.exportFuncAddrs ((sh cs₀).frame f).module =
      I.addrs.map ((cs₀ : Store _).funcs.length + ·) := by
    rw [Shift.frame_module, exportFuncAddrs_minst, haddr]
    rfl
  refine ⟨r, ((sh cs₀).frame f).module, hrs, hostsSat_instantiateOnce (trampsP_hosts inst fid) hr,
    ⟨hprep, fun fr hfr => coreImportsFor_trampL hc hi cs₀ inst fid fr hfr, fun x hx => ?_⟩⟩
  obtain ⟨n, hn⟩ := hc.core x hx
  have hname : coreNameI c x = n := by rw [coreNameI, hn]; rfl
  rw [hname]
  exact lookup_funcExport_gen hi.names hIs.valid ho₂ ha hn

/-! ## The parent instantiation without `CoreFactsL` -/

section Link

open Silmaril.Wasm.Component.Machine

variable {σ : Type}

/-- **The results of instantiating `l.toRef`, from `Inst` of both children**, under any host:
for an importer module without data and element segments, there are the exporter's game
instance `Ie` and core store `cse` (`CoreFacts`), and for every game instance `Ii` of the
importer module a store `r` (second projection `Ii.store`, host code the trampolines paired with
their import index) such that the only result of instantiating `l.toRef` is the instance at
`afterLink` over the core store `reloc cse (r.mapH Prod.fst)` with root instance `0` and export
map `exportMapL l`. -/
theorem instBehavioursL_inst {l : Linked2} (hEg : l.exp.Good) (hEi : l.exp.Inst)
    (hIg : l.imp.Good) (hIi : l.imp.Inst) (hIa : l.imp.Arity)
    (hseg : l.imp.mod.mod.data = [] ∧ l.imp.mod.mod.elems = []) (hW : l.WireTy)
    (hN : l.NamesOk) :
    ∃ (Ie : Silmaril.Wasm.Game.ScalarInstance) (cse : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR)))
      (cie : (core3R Pf V IR).Inst), CoreFacts l.exp Ie cse cie ∧
      ∀ (Ii : Silmaril.Wasm.Game.ScalarInstance), l.imp.mod.IsInst Ii →
      ∃ r : Store (CanonHost (core3R Pf V IR) × Nat), Store.mapH Prod.snd r = Ii.store ∧
        HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
          h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r ∧
        ∀ (prof : ProfileKind) (h : Host (core3R Pf V IR) σ) (h₀ : σ),
        ∀ res ∈ instBehaviours prof h (initConfig h₀) l.toRef [],
          res = .instance (afterLink Pf (reloc cse (Store.mapH Prod.fst r))
            (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀) ⟨0⟩
            (exportMapL l) := by
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := Pf) (V := V) (IR := IR) hEg hEi
  refine ⟨Ie, cse, cie, hFe, fun Ii hI => ?_⟩
  obtain ⟨r, cii, hrs, hh, hFi⟩ := coreFactsL_of_inst hIg hIi hseg hI cse ⟨2⟩ l.wireFid
  exact ⟨r, hrs, hh, fun prof h h₀ =>
    instBehavioursL_toRef hEg hFe hIg hIa hIi.importNames hW hN hFi prof h h₀⟩

end Link

end Silmaril.Proofs.Wasm.Component.Param.Core3R
