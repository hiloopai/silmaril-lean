module

public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Proofs.Wasm.Game.Instantiate.Basic
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# Spec-faithful instances: proofs

* `IsSpecInstanceAt.instantiate`: the configuration `c₀` of a spec instance at
  `s` is the configuration of the specification's `$instantiate` into `s`, for
  every profile and host (`prepare?_sound`);
* `IsSpecInstanceAt.ok`: it is typed at `[]` (silmaril-lean's `Instantiate.ok`)
  and the instance is well formed at its store: the store is `s` extended by the
  module's own (Wasm) functions (`prepare?_funcs`), so its host functions are
  those of `s` (`wellFormed_of_funcs`);
* `IsSpecInstance.toAt`: fresh host functions (`importStore`) are a typed store
  whose host functions are the imports (`importStore_hostTyped`), and the
  import addresses have the import types (`importAddrs_typed`).

New proofs; `importStore_hostTyped` and `wellFormed_of_funcs` split the proof of
`IsInstanceStart.ok_store` (`Silmaril.Proofs.Wasm.Game.Start.Instance`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecInst

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.InstantiateAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The thread of a configuration denotes the configuration. -/
theorem configThread_config (c : Config Nat) : (configThread c).config c.store = c := rfl

/-- The import addresses have the module's import types in `importStore`. -/
theorem importAddrs_typed {mt : CModuleType} (hf : ∀ xt ∈ mt.imports, ∃ d, xt = .func d) :
    List.Forall₂ (ExternAddrOk (importStore (CExternType.funcs mt.imports))) (importAddrs mt)
      mt.imports := by
  simpa only [importAddrs, funcs_map_func hf] using importAddrs_ok (CExternType.funcs mt.imports)

/-- The validity premise of `$instantiate` for the import addresses. -/
theorem importAddrs_valid {m : Module} {mt : CModuleType} (hv : validate? m = some mt)
    (hf : ∀ xt ∈ mt.imports, ∃ d, xt = .func d) :
    ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk (importStore (CExternType.funcs mt.imports))) (importAddrs mt)
        xtI :=
  ⟨mt.exports, mt.imports, validate?_sound hv, importAddrs_typed hf⟩

/-- **The configuration of a spec instance is the configuration of `$instantiate`**, for every
profile and host. -/
theorem IsSpecInstance.instantiate {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (h : IsSpecInstance m mt I c₀) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics Nat) :
    Instantiate P host (importStore (CExternType.funcs mt.imports)) m (importAddrs mt) c₀ := by
  obtain ⟨c, st, hp, rfl, -, -⟩ := h.prepared
  exact (prepare?_sound evalConst?_evalSound hp (importAddrs_valid h.valid h.funcImports)).2

/-- The store of a spec instance is the store of its configuration. -/
theorem IsSpecInstance.store_eq {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (h : IsSpecInstance m mt I c₀) : c₀.store = I.store := by
  obtain ⟨c, st, -, rfl, hs, -⟩ := h.prepared
  cases st <;> exact hs

/-- The stages of `prepare?`. -/
theorem prepare?_inv {s : Store Nat} {m : Module} {xas : List ExternAddr} {c : Config Nat}
    {st : Option FuncIdx} (hp : prepare? evalConst? s m xas = some (c, st)) :
    ∃ s₁ f₁ valsG s₂ f₂ refsT s₃ f₃ refsE s₄ mi,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
        (m.globals.map Global.init) = some (s₁, f₁, valsG) ∧
      evalExprs? evalConst? s₁ f₁ (m.tables.map Table.init) = some (s₂, f₂, refsT) ∧
      evalExprss? evalConst? s₂ f₂ (m.elems.map Elem.init) = some (s₃, f₃, refsE) ∧
      allocModule? s₃ m xas valsG refsT refsE = some (s₄, mi) ∧ c.store = s₄ := by
  unfold prepare? at hp
  split at hp
  · split at hp
    · cases hp
    rename_i s₁ f₁ valsG hG
    split at hp
    · cases hp
    rename_i s₂ f₂ refsT hT
    split at hp
    · cases hp
    rename_i s₃ f₃ refsE hE
    split at hp
    · cases hp
    rename_i s₄ mi hM
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hp)
    exact ⟨s₁, f₁, valsG, s₂, f₂, refsT, s₃, f₃, refsE, s₄, mi, hG, hT, hE, hM, rfl⟩
  · cases hp

/-- **The functions of a prepared store**: the functions of the original store, then the
module's Wasm functions. -/
theorem prepare?_funcs {s : Store Nat} {m : Module} {xas : List ExternAddr} {c : Config Nat}
    {st : Option FuncIdx} (hp : prepare? evalConst? s m xas = some (c, st)) :
    ∃ new : List (FuncInst Nat), c.store.funcs = s.funcs ++ new ∧
      ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  obtain ⟨s₁, f₁, valsG, s₂, f₂, refsT, s₃, f₃, refsE, s₄, mi, hG, hT, hE, hM, hc⟩ :=
    prepare?_inv hp
  have h₁ : s₁.funcs = s.funcs := (evalGlobals?_shape hG).2.1
  have h₂ : s₂.funcs = s₁.funcs := (evalExprs?_shape hT).2.1
  have h₃ : s₃.funcs = s₂.funcs := (evalExprss?_shape hE).2.1
  obtain ⟨tagTypes, funcTypes, xi, -, -, -, -, hs₄⟩ := allocModule?_inv hM
  rw [hc, hs₄]
  refine ⟨_, by rw [h₃, h₂, h₁], ?_⟩
  intro fi hfi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hfi
  exact ⟨p.2, rfl⟩

/-- **The host functions of `importStore` are the imports**, of their scalar types. -/
theorem importStore_hostTyped {mt : CModuleType} {I : ScalarInstance}
    (himp : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
      (CExternType.funcs mt.imports) I.imports) :
    I.HostTyped (importStore (CExternType.funcs mt.imports)) := by
  intro a fi hh hfa hcode
  have hlenI : (CExternType.funcs mt.imports).length = I.imports.length := himp.length_eq
  have ha : a < (CExternType.funcs mt.imports).length := by
    simpa [importStore] using (List.getElem?_eq_some_iff.mp hfa).1
  have hfi : fi = { type := (CExternType.funcs mt.imports)[a], module := {}, code := .host a } :=
    Option.some.inj (hfa.symm.trans (importStore_funcs_getElem? _ ha))
  have hah : a = hh := by rw [hfi] at hcode; cases hcode; rfl
  have hlt : hh < I.imports.length := hah ▸ hlenI ▸ ha
  have hty : FnType.ofDefType? fi.type = some (I.imports.get ⟨hh, hlt⟩) := by
    rw [hfi]
    exact hah ▸ (List.forall₂_iff_get.mp himp).2 a ha (hah ▸ hlt)
  exact ⟨hlt, FnType.expand_of_ofDefType? hty⟩

/-- **Well-formedness from the shape of the functions**: a typed store whose functions are those
of a store with typed host functions followed by Wasm functions, with exports of the scalar
export types, is a well-formed store of the instance. -/
theorem wellFormed_of_funcs {I : ScalarInstance} {s s' : Store Nat} (hS : StoreOk s')
    (hhost : I.HostTyped s)
    (hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, s'.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports)
    {new : List (FuncInst Nat)} (hfuncs : s'.funcs = s.funcs ++ new)
    (hwasm : ∀ fi ∈ new, ∃ code, fi.code = .wasm code) : I.WellFormed s' := by
  have hlenE : I.addrs.length = I.exports.length := hexp.length_eq
  refine ⟨hS, hlenE, fun j => ?_, fun a fi hh hfa hcode => ?_⟩
  · have hj : (j : Nat) < I.addrs.length := by rw [hlenE]; exact j.2
    obtain ⟨fi, hfi, hft⟩ := (List.forall₂_iff_get.mp hexp).2 j hj j.2
    refine ⟨fi, ?_, FnType.expand_of_ofDefType? hft⟩
    simpa [Silmaril.Wasm.Game.ScalarInstance.addr, List.getD_eq_getElem?_getD, hj] using hfi
  · show ∃ hlt : hh < I.imports.length, Expand fi.type (I.imports.get ⟨hh, hlt⟩).toComp
    have hfa' : (s.funcs ++ new)[a]? = some fi := hfuncs ▸ hfa
    rcases Nat.lt_or_ge a s.funcs.length with ha | ha
    · exact hhost a fi hh ((List.getElem?_append_left ha).symm.trans hfa') hcode
    · have hnew' : new[a - s.funcs.length]? = some fi :=
        (List.getElem?_append_right ha).symm.trans hfa'
      obtain ⟨code, hc⟩ := hwasm fi (List.mem_of_getElem? hnew')
      cases hc.symm.trans hcode

/-- A spec instance into `importStore` is a spec instance at `importStore`. -/
theorem IsSpecInstance.toAt {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (h : IsSpecInstance m mt I c₀) :
    IsSpecInstanceAt (importStore (CExternType.funcs mt.imports)) (importAddrs mt) m mt I c₀ where
  valid := h.valid
  storeOk := importStore_ok h.valid h.funcImports
  importsOk := importAddrs_typed h.funcImports
  hostTyped := importStore_hostTyped h.importTypes
  prepared := h.prepared
  exportTypes := h.exportTypes

/-- **The configuration of a spec instance at `s` is the configuration of `$instantiate`**, for
every profile and host. -/
theorem IsSpecInstanceAt.instantiate {s : Store Nat} {xas : List ExternAddr} {m : Module}
    {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (h : IsSpecInstanceAt s xas m mt I c₀) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics Nat) : Instantiate P host s m xas c₀ := by
  obtain ⟨c, st, hp, rfl, -, -⟩ := h.prepared
  exact (prepare?_sound evalConst?_evalSound hp
    ⟨mt.exports, mt.imports, validate?_sound h.valid, h.importsOk⟩).2

/-- The store of a spec instance at `s` is the store of its configuration. -/
theorem IsSpecInstanceAt.store_eq {s : Store Nat} {xas : List ExternAddr} {m : Module}
    {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (h : IsSpecInstanceAt s xas m mt I c₀) : c₀.store = I.store := by
  obtain ⟨c, st, -, rfl, hs, -⟩ := h.prepared
  cases st <;> exact hs

/-- **Spec instances at `s` are typed and well formed**: the configuration of `$instantiate` is
typed at `[]`, and the instance is well formed at its store. -/
theorem IsSpecInstanceAt.ok {s : Store Nat} {xas : List ExternAddr} {m : Module}
    {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (h : IsSpecInstanceAt s xas m mt I c₀) : ConfigOk c₀ [] ∧ I.WellFormed c₀.store := by
  have hc : ConfigOk c₀ [] :=
    Instantiate.ok (P := profile neverFail) SingleThreaded.divHost_ok h.storeOk
      (IsSpecInstanceAt.instantiate h (profile neverFail) SingleThreaded.divHost)
  obtain ⟨c, st, hp, hc₀, hstore, -⟩ := h.prepared
  obtain ⟨new, hfuncs, hwasm⟩ := prepare?_funcs hp
  have hst : c₀.store = c.store := by rw [hc₀]; cases st <;> rfl
  have hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, c₀.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports := by
    rw [hst, hstore]
    exact h.exportTypes
  exact ⟨hc, wellFormed_of_funcs (SingleThreaded.ConfigOk.storeOk hc) h.hostTyped
    hexp (hst ▸ hfuncs) hwasm⟩

/-- **Spec instances are typed and well formed.** -/
theorem IsSpecInstance.ok {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (h : IsSpecInstance m mt I c₀) :
    ConfigOk c₀ [] ∧ I.WellFormed c₀.store :=
  IsSpecInstanceAt.ok (IsSpecInstance.toAt h)

end Silmaril.Proofs.Wasm.Game.SpecInst
