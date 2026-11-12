module

public import Silmaril.Wasm.Game.Start.Defs
public import Silmaril.Proofs.Wasm.Game.Instantiate.Basic
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck

/-!
# Instances with a start function are well formed: proofs

* `isInstanceStart_none_iff`: `IsInstance` is the start-free case of
  `IsInstanceStart`.
* `IsInstanceStart.ok`: the instance before its start function is well formed
  (the proof of `IsInstance.ok`, with the start call kept in the typed
  configuration that `instantiateOnce?` reaches), and the start function has
  the type `[] → []` (`startTyped_of_configOk`: the typed configuration
  `call x` at `[] → []` names a function of that type).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.InstantiateAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- **The instances without start function are the start-free special case.** -/
theorem isInstanceStart_none_iff {m : Module} {mt : CModuleType} {I : ScalarInstance} :
    IsInstanceStart m mt I none ↔ IsInstance m mt I := by
  constructor
  · rintro ⟨hv, hf, hi, ⟨f, st, h, ha, hr⟩, he⟩
    cases hr
    exact ⟨hv, hf, hi, ⟨f, h, ha⟩, he⟩
  · rintro ⟨hv, hf, hi, ⟨f, h, ha⟩, he⟩
    exact ⟨hv, hf, hi, ⟨f, none, h, ha, .none⟩, he⟩

/-- The typed configuration reached by `instantiateOnce?`, with its start call, and the
functions it adds (all Wasm functions). -/
theorem instantiateOnce?_typed {m : Module} {mt : CModuleType} (hv : validate? m = some mt)
    (hf : ∀ xt ∈ mt.imports, ∃ d, xt = .func d) {s' : Store Nat} {f : Frame}
    {st : Option FuncIdx}
    (hi : instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
      ((List.range mt.imports.length).map ExternAddr.func) = some (s', f, st)) :
    ConfigOk ⟨s', f, startCode st⟩ [] ∧
      ∃ new : List (FuncInst Nat),
        s'.funcs = (importStore (CExternType.funcs mt.imports)).funcs ++ new ∧
        ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  have hs : StoreOk (importStore (CExternType.funcs mt.imports)) := importStore_ok hv hf
  have hxas : List.Forall₂ (ExternAddrOk (importStore (CExternType.funcs mt.imports)))
      ((List.range mt.imports.length).map ExternAddr.func) mt.imports := by
    simpa only [funcs_map_func hf] using importAddrs_ok (CExternType.funcs mt.imports)
  have hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk (importStore (CExternType.funcs mt.imports)))
        ((List.range mt.imports.length).map ExternAddr.func) xtI :=
    ⟨mt.exports, mt.imports, validate?_sound hv, hxas⟩
  obtain ⟨s₁, f₁, vs, c, hg, hp, hS⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail)
    (host := SingleThreaded.divHost) hi
  obtain ⟨s₁', f₁', vs', c', hg', hp', hS'⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail) (host := fun _ _ _ _ => False) hi
  obtain ⟨rfl, rfl, rfl⟩ : s₁ = s₁' ∧ f₁ = f₁' ∧ vs = vs' := by simpa using hg.symm.trans hg'
  obtain rfl : c = c' := by simpa using hp.symm.trans hp'
  obtain ⟨hc, -, new, hnew, hwasm⟩ :=
    prepare?_globalResidue_ok (P := SingleThreaded.profile SingleThreaded.neverFail)
      SingleThreaded.divHost_ok hs hvalid hg hp
  have hS₂ : Steps (SingleThreaded.profile SingleThreaded.neverFail) SingleThreaded.divHost
      (c.withStart st) ⟨s', f, startCode st⟩ := by
    rw [← Config.withStart_nil]
    exact Steps.withStart hS
  have hc' : ConfigOk ⟨s', f, startCode st⟩ [] := steps_configOk SingleThreaded.divHost_ok hc hS₂
  have hfuncs : s'.funcs = (importStore (CExternType.funcs mt.imports)).funcs ++ new :=
    (steps_funcs_eq hS').trans hnew
  exact ⟨hc', new, hfuncs, hwasm⟩

/-- A typed `call x` at `[] → []` names a function of type `[] → []`. -/
theorem startTyped_of_configOk {s : Store Nat} {f : Frame} {x : FuncIdx} {a : Nat}
    (h : ConfigOk ⟨s, f, [.plain (.call x)]⟩ []) (hx : f.module.funcs[x.toNat]? = some a) :
    StartTyped s a := by
  obtain ⟨C, ⟨hs, hfr⟩, hadm⟩ := h
  have hΔ : C.toTypeCtx.Ok := FrameOk.toTypeCtx_okReg hs hfr
  obtain ⟨ts, it₀, ha, hp, hr, -⟩ := AdminsOk.single_inv hΔ hadm
  obtain ⟨d, ps, rs, hd, he, rfl⟩ := PC.inv_call ha
  have hps : ps.toList = [] :=
    (List.append_eq_nil_iff.mp (List.forall₂_nil_left_iff.mp hp)).2
  have hrs : rs.toList = [] :=
    (List.append_eq_nil_iff.mp (List.forall₂_nil_right_iff.mp hr)).2
  obtain ⟨a', ha', hea⟩ := FrameOk.func hfr hd
  have haa : a' = a := Option.some.inj (ha'.symm.trans hx)
  obtain ⟨xt', e, hsub, hok⟩ := ExternAddrOk.principal hs hea
  obtain ⟨fi, hfi, rfl⟩ : ∃ fi, s.funcs[a']? = some fi ∧ CExternType.func fi.type = xt' := by
    simpa only [externAddrType?, Option.map_eq_some_iff] using e
  cases hsub with
  | func hsubd =>
    show StartTyped s a
    cases hok with
    | func hdok _ =>
      show StartTyped s a
      have hfit : TyOk {} fi.type := by
        cases hs.funcs fi (List.mem_of_getElem? hfi) <;> assumption
      obtain ⟨ps', rs', he', hps', hrs'⟩ := PC.func_sub_data (.inr ⟨hdok, hsubd⟩) hfit he
      have hps'' : ps'.toList = [] := List.forall₂_nil_left_iff.mp (hps ▸ hps')
      have hrs'' : rs'.toList = [] := List.forall₂_nil_right_iff.mp (hrs ▸ hrs')
      have e1 : ps' = Ty.ofList [] := by rw [← Ty.ofList_toList ps', hps'']
      have e2 : rs' = Ty.ofList [] := by rw [← Ty.ofList_toList rs', hrs'']
      have hst : Expand fi.type startType.toComp := by
        rw [e1, e2] at he'
        exact he'
      exact ⟨fi, haa ▸ hfi, hst⟩

/-- **Instances before their start function are well formed.** -/
theorem IsInstanceStart.ok_store {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {start : Option Nat} (h : IsInstanceStart m mt I start) : I.Ok := by
  obtain ⟨hv, hf, himp, ⟨f, st, hi, -, -⟩, hexp⟩ := h
  obtain ⟨hc', new, hfuncs, hwasm⟩ := instantiateOnce?_typed hv hf hi
  have hlenI : (CExternType.funcs mt.imports).length = I.imports.length := himp.length_eq
  have hlenE : I.addrs.length = I.exports.length := hexp.length_eq
  refine ⟨SingleThreaded.ConfigOk.storeOk hc', hlenE, fun j => ?_, fun a fi hh hfa hcode => ?_⟩
  · have hj : (j : Nat) < I.addrs.length := by rw [hlenE]; exact j.2
    obtain ⟨fi, hfi, hft⟩ := (List.forall₂_iff_get.mp hexp).2 j hj j.2
    refine ⟨fi, ?_, FnType.expand_of_ofDefType? hft⟩
    simpa [Silmaril.Wasm.Game.ScalarInstance.addr, List.getD_eq_getElem?_getD, hj] using hfi
  · show ∃ hlt : hh < I.imports.length, Expand fi.type (I.imports.get ⟨hh, hlt⟩).toComp
    have hfa' : ((importStore (CExternType.funcs mt.imports)).funcs ++ new)[a]? = some fi :=
      hfuncs ▸ hfa
    rcases Nat.lt_or_ge a (importStore (CExternType.funcs mt.imports)).funcs.length with ha | ha
    · have ha' : a < (CExternType.funcs mt.imports).length := by simpa [importStore] using ha
      obtain rfl : fi = { type := (CExternType.funcs mt.imports)[a], module := {}, code := .host a } :=
        Option.some.inj (((List.getElem?_append_left ha).symm.trans hfa').symm.trans
          (importStore_funcs_getElem? _ ha'))
      obtain rfl : a = hh := by cases hcode; rfl
      have hlt : a < I.imports.length := hlenI ▸ ha'
      exact ⟨hlt, FnType.expand_of_ofDefType? ((List.forall₂_iff_get.mp himp).2 a ha' hlt)⟩
    · have hnew' : new[a - (importStore (CExternType.funcs mt.imports)).funcs.length]? = some fi :=
        (List.getElem?_append_right ha).symm.trans hfa'
      obtain ⟨code, hc⟩ := hwasm fi (List.mem_of_getElem? hnew')
      cases hc.symm.trans hcode

/-- The start function of an instance has type `[] → []`. -/
theorem IsInstanceStart.startTyped {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {start : Option Nat} (h : IsInstanceStart m mt I start) :
    ∀ a ∈ start, StartTyped I.store a := by
  obtain ⟨hv, hf, -, ⟨f, st, hi, -, hr⟩, -⟩ := h
  obtain ⟨hc', -⟩ := instantiateOnce?_typed hv hf hi
  intro a ha
  cases hr with
  | none => cases ha
  | some hxa =>
    cases ha
    exact startTyped_of_configOk hc' hxa

end Silmaril.Proofs.Wasm.Game
