module

public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Proofs.Wasm.Game.Instantiate.Residue
public import Silmaril.Wasm.Validation.RollClosed
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness

/-!
# Instances of modules are well formed: proofs

`IsInstance.ok`: `StoreOk (importStore ds)` from validity of the closed import
types, `ExternAddrOk` of the import addresses by construction, and the typing
of `instantiateOnce?` (`Silmaril.Proofs.Wasm.Game.Instantiate.Residue`);
instantiation only adds Wasm functions, so the host functions of the instance
store are those of `importStore ds`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.InstantiateAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### Helpers -/

theorem mem_funcs_of_mem {d : DefType} :
    ∀ {xs : List CExternType}, d ∈ CExternType.funcs xs → CExternType.func d ∈ xs
  | [], h => by cases h
  | .func d' :: xs, h => by
    simp only [CExternType.funcs, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_funcs_of_mem h)
  | .tag _ :: _, h | .global _ :: _, h | .mem _ :: _, h | .table _ :: _, h =>
    List.mem_cons_of_mem _ (mem_funcs_of_mem h)

theorem funcs_map_func :
    ∀ {xs : List CExternType}, (∀ xt ∈ xs, ∃ d, xt = .func d) →
      (CExternType.funcs xs).map CExternType.func = xs
  | [], _ => rfl
  | xt :: xs, h => by
    obtain ⟨d, rfl⟩ := h xt (List.mem_cons_self ..)
    simp only [CExternType.funcs, List.map_cons]
    rw [funcs_map_func fun xt hxt => h xt (List.mem_cons_of_mem _ hxt)]

theorem forall₂_mem_right' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => by cases hb
  | a :: _, _, .cons hab hrest, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨a', ha', h⟩ := forall₂_mem_right' hrest b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h⟩

/-- Only a function extern type closes to a function type. -/
private theorem closeExtern?_eq_func {C : Context} {t : ExternType} {d : DefType}
    (h : C.closeExtern? t = some (.func d)) : ∃ x, t = .func x ∧ C.type? x = some d := by
  cases t with
  | func x =>
    obtain ⟨d', hx, hdd⟩ := Option.map_eq_some_iff.1 h
    cases hdd
    exact ⟨x, rfl, hx⟩
  | tag x =>
    obtain ⟨_, -, h'⟩ := Option.map_eq_some_iff.1 h
    cases h'
  | global g => cases h
  | memory _ => cases h
  | table _ => cases h

/-- A function import type of a valid module is closed and expands to a function type. -/
theorem funcImport_ok {m : Module} {mt : CModuleType} (hv : validate? m = some mt)
    {d : DefType} (hd : CExternType.func d ∈ mt.imports) :
    TyOk {} d ∧ ∃ ps rs, Expand d (.func ps rs) := by
  have hm : ModuleOk m ⟨mt.imports, mt.exports⟩ := validate?_sound hv
  cases hm with
  | @mk dts _ _ _ _ _ _ _ _ _ htypes himports =>
    obtain ⟨im, -, hc, hok⟩ := forall₂_mem_right' himports _ hd
    obtain ⟨_, -, hx⟩ := closeExtern?_eq_func hc
    have hdts : d ∈ dts := List.mem_of_getElem? hx
    cases hok with
    | func _ he => exact ⟨htypes.tyOk_empty' _ hdts, _, _, he⟩

theorem importStore_funcs_getElem? (ds : List DefType) {i : Nat} (hi : i < ds.length) :
    (importStore ds).funcs[i]? = some { type := ds[i], module := {}, code := .host i } := by
  simp [importStore, hi]

/-- The import addresses `0, …, |ds| - 1` have the types `ds` in `importStore ds`. -/
theorem importAddrs_ok (ds : List DefType) :
    List.Forall₂ (ExternAddrOk (importStore ds))
      ((List.range (ds.map CExternType.func).length).map ExternAddr.func)
      (ds.map CExternType.func) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  have hi : i < ds.length := by simpa using h₂
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact ExternAddrOk.func (fi := { type := ds[i], module := {}, code := .host i })
    (importStore_funcs_getElem? ds hi)

/-- Host-free runs never change the function instances. -/
theorem steps_funcs_eq {P : Silmaril.Wasm.Numerics.Profile} {c c' : Config Nat}
    (h : Steps P (fun _ _ _ _ => False) c c') : c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hst ih => exact (SingleThreaded.Step.framesLocal hst).1.trans ih

/-- Runs from a typed configuration stay typed. -/
theorem steps_configOk {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}
    (hhost : HostOk host) {c c' : Config Nat} {ts : List CValType} (hc : ConfigOk c ts)
    (h : Steps P host c c') : ConfigOk c' ts := by
  induction h with
  | refl => exact hc
  | tail _ hst ih => exact (Step.preservation hhost ih hst).1

/-- `importStore` is well typed for validated closed import types. -/
theorem importStore_ok {m : Module} {mt : CModuleType} (hv : validate? m = some mt)
    (hf : ∀ xt ∈ mt.imports, ∃ d, xt = .func d) :
    StoreOk (importStore (CExternType.funcs mt.imports)) := by
  have _hf := hf
  have hd : ∀ d ∈ CExternType.funcs mt.imports, TyOk {} d ∧ ∃ ps rs, Expand d (.func ps rs) :=
    fun d hd => funcImport_ok hv (mem_funcs_of_mem hd)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [importStore]; done)
  intro fi hfi
  simp only [importStore, List.mem_mapIdx] at hfi
  obtain ⟨i, hi, rfl⟩ := hfi
  obtain ⟨hok, ps, rs, he⟩ := hd _ (List.getElem_mem hi)
  exact FuncInstOk.host hok he rfl

/-- **Instances of modules are well formed.** -/
theorem IsInstance.ok {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : IsInstance m mt I) : I.Ok := by
  obtain ⟨hv, hf, himp, ⟨f, hi, -⟩, hexp⟩ := h
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
      (c.withStart none) ⟨I.store, f, startCode none⟩ := by
    rw [← Config.withStart_nil]
    exact Steps.withStart hS
  have hc' : ConfigOk ⟨I.store, f, startCode none⟩ [] :=
    steps_configOk SingleThreaded.divHost_ok hc hS₂
  have hfuncs : I.store.funcs = (importStore (CExternType.funcs mt.imports)).funcs ++ new :=
    (steps_funcs_eq hS').trans hnew
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

theorem forall₂_functional {α β : Type} {R : α → β → Prop}
    (hR : ∀ a b b', R a b → R a b' → b = b') :
    ∀ {l : List α} {l₁ l₂ : List β}, List.Forall₂ R l l₁ → List.Forall₂ R l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [hR _ _ _ h₁ h₂, forall₂_functional hR t₁ t₂]

/-- The instance of a module is unique. -/
theorem IsInstance.unique {m : Module} {mt : CModuleType} {I J : Silmaril.Wasm.Game.ScalarInstance}
    (hI : IsInstance m mt I) (hJ : IsInstance m mt J) : I = J := by
  obtain ⟨-, -, himpI, ⟨fI, hiI, haI⟩, hexpI⟩ := hI
  obtain ⟨-, -, himpJ, ⟨fJ, hiJ, haJ⟩, hexpJ⟩ := hJ
  have himp : I.imports = J.imports :=
    forall₂_functional (fun _ _ _ h h' => Option.some.inj (h.symm.trans h')) himpI himpJ
  rw [hiI] at hiJ
  simp only [Option.some.injEq, Prod.mk.injEq] at hiJ
  obtain ⟨hst, rfl, -⟩ := hiJ
  have haddr : I.addrs = J.addrs := haI.symm.trans haJ
  have hexp : I.exports = J.exports := by
    rw [← haddr] at hexpJ
    rw [← hst] at hexpJ
    refine forall₂_functional (fun a b b' h h' => ?_) hexpI hexpJ
    obtain ⟨fi, hfi, hb⟩ := h
    obtain ⟨fi', hfi', hb'⟩ := h'
    rw [hfi] at hfi'
    cases hfi'
    exact Option.some.inj (hb.symm.trans hb')
  cases I; cases J
  simp_all

end Silmaril.Proofs.Wasm.Game
