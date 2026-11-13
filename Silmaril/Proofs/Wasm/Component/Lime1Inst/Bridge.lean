module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Prepare
public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Exports

/-!
# The Lime1 instantiation bridge for global-free modules

Proofs in `Lime1Inst.{Retract,Alloc,Prepare,Exports}`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref Silmaril.Wasm.Component.Lime1Bridge
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)
open Silmaril.Wasm.Lime1.Execution (Prepared)

/-- The Lime1 engine instance of a module without imports: a preparation from the empty store,
without start function, whose exports are looked up by name. -/
theorem instOf_inv {m : Silmaril.Wasm.Lime1.Module} {exps : CoreIface} {I : EInstance lime1}
    (h : instOf lime1 m [] exps = some I) :
    ∃ p : Prepared Nat, Silmaril.Wasm.Lime1.Execution.prepare? {} m [] = some p ∧
      exportAddrs lime1 p.module exps = some I.addrs ∧ I.store = p.store := by
  simp only [instOf, allocHosts, Silmaril.Wasm.Component.Engine.Lime1.lime1,
    Silmaril.Wasm.Component.Engine.Lime1.prepare?, List.map_nil] at h
  split at h
  · rename_i s' inst hp
    simp only [Option.map_eq_some_iff] at hp h
    obtain ⟨p, hp, hpe⟩ := hp
    obtain ⟨addrs, ha, rfl⟩ := h
    simp only [Prod.mk.injEq] at hpe
    obtain ⟨rfl, rfl, -⟩ := hpe
    exact ⟨p, hp, ha, rfl⟩
  · cases h

theorem imports_nil_of_funcs {xs : List Silmaril.Wasm.Validation.CExternType}
    (hf : ∀ xt ∈ xs, ∃ d, xt = .func d) (h : Silmaril.Wasm.Validation.CExternType.funcs xs = []) :
    xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    obtain ⟨d, rfl⟩ := hf x (by simp)
    simp [Silmaril.Wasm.Validation.CExternType.funcs] at h

theorem moduleOk_imports_length {M : Silmaril.Wasm.Module}
    {mt : Silmaril.Wasm.Validation.CModuleType} (h : Silmaril.Wasm.Validation.ModuleOk M mt) :
    M.imports.length = mt.imports.length := by
  cases h with
  | mk _ himports => exact himports.length_eq

/-- An instance of an import-free `NumModule` instantiates a module without imports. -/
theorem isInst_imports {M : Silmaril.Wasm.Module} {mt : Silmaril.Wasm.Validation.CModuleType}
    {I' : Silmaril.Wasm.Game.ScalarInstance} (hIs : Silmaril.Wasm.Game.IsInstance M mt I')
    (himp : I'.imports = []) : mt.imports = [] ∧ M.imports = [] := by
  have hfn : Silmaril.Wasm.Validation.CExternType.funcs mt.imports = [] := by
    have h := hIs.importTypes
    rw [himp] at h
    exact List.forall₂_nil_right_iff.mp h
  have hmt := imports_nil_of_funcs hIs.funcImports hfn
  refine ⟨hmt, ?_⟩
  have hlen := moduleOk_imports_length (Silmaril.Wasm.Validation.validate?_sound hIs.valid)
  rw [hmt] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

theorem retract_data {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) : l.data.map Silmaril.Wasm.Lime1.Data.toCore = M.data :=
  congrArg Silmaril.Wasm.Module.data hret

theorem retract_elems {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) :
    l.elems.map Silmaril.Wasm.Lime1.Elem.toCore = M.elems.map funcrefElem :=
  congrArg Silmaril.Wasm.Module.elems hret

theorem retract_globals {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) : l.globals.map Silmaril.Wasm.Lime1.Global.toCore = M.globals :=
  congrArg Silmaril.Wasm.Module.globals hret

theorem retract_imports {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) : l.imports.map Silmaril.Wasm.V1.Import.toCore = M.imports :=
  congrArg Silmaril.Wasm.Module.imports hret

theorem retract_exports {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) : l.exports.map Silmaril.Wasm.V1.Export.toCore = M.exports :=
  congrArg Silmaril.Wasm.Module.exports hret

/-- The Core module, with its own element segments, is the image with these segments. -/
theorem withElems_retract {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) : withElems l M.elems = M := by
  rw [withElems, hret]; rfl

/-- **The copied side conditions hold** for a Lime1 module decoded from a Core module whose
instantiation is defined, from the empty store, when the module has no globals. -/
theorem bounds_gen {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) (hg : M.globals = [])
    {before : Silmaril.Wasm.Lime1.Execution.Store Nat}
    (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF before)
    (htab : ∀ t ∈ before.tables, t.refs.length < 2 ^ 32)
    (hb : M.elems.length ≤ 2 ^ 32 ∧ M.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ M.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ M.elems, e.init.length < 2 ^ 32)) :
    Silmaril.Wasm.Lime1.Execution.InstantiationBounds before l := by
  have hD := retract_data hret
  have hE := retract_elems hret
  have hEl : l.elems.length = M.elems.length := by
    simpa only [List.length_map] using congrArg List.length hE
  have hDl : l.data.length = M.data.length := by
    simpa only [List.length_map] using congrArg List.length hD
  have hgl : l.globals = [] := by
    simpa only [hg, List.map_eq_nil_iff] using retract_globals hret
  refine ⟨hwf, hgl, htab, fun d hd => ?_, fun e he => ?_, hEl ▸ hb.1, hDl ▸ hb.2.1⟩
  · have hm : Silmaril.Wasm.Lime1.Data.toCore d ∈ M.data := hD ▸ List.mem_map_of_mem hd
    exact hb.2.2.1 _ hm
  · have hm : Silmaril.Wasm.Lime1.Elem.toCore e ∈ M.elems.map funcrefElem :=
      hE ▸ List.mem_map_of_mem he
    obtain ⟨e', he', heq⟩ := List.mem_map.mp hm
    have hi : e'.init.length = e.init.length := by
      have := congrArg (fun x => x.init.length) heq
      simpa [funcrefElem, Silmaril.Wasm.Lime1.Elem.toCore] using this
    exact hi ▸ hb.2.2.2 e' he'

theorem bounds_of {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) (hg : M.globals = [])
    (hb : M.elems.length ≤ 2 ^ 32 ∧ M.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ M.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ M.elems, e.init.length < 2 ^ 32)) :
    Silmaril.Wasm.Lime1.Execution.InstantiationBounds
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) l :=
  bounds_gen hret hg ⟨fun _ _ _ _ h => by simp at h, fun _ _ h => by simp at h⟩ (by simp) hb

theorem mapM_fst {α β γ : Type _} (f : α → Option γ) :
    ∀ xs : List (α × β), xs.mapM (fun x => f x.1) = (xs.map Prod.fst).mapM f
  | [] => rfl
  | x :: xs => by simp only [List.mapM_cons, List.map_cons, mapM_fst f xs]

/-- **The name-based export addresses are the function addresses in export order** (part (b)):
the engine looks up the IR's export names, which are the module's function export names in
order (`Simple.Inst.names`), among export instances with distinct names. -/
theorem exportAddrs_eq {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid l)
    (hg : l.globals = []) {before : Silmaril.Wasm.Lime1.Execution.Store Nat} {p : Prepared Nat}
    {imports : List Silmaril.Wasm.Execution.Runtime.ExternVal}
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? before l imports = some p) {exps : CoreIface}
    (hnames : funcExportNames M = exps.map (·.1)) {addrs : List lime1.FuncAddr}
    (ha : exportAddrs lime1 p.module exps = some addrs) :
    addrs = funcAddrs p.module.exports := by
  obtain ⟨allocated, -, -, hal, -, -, -⟩ := Silmaril.Wasm.Lime1.Execution.prepare?_inv hp
  obtain ⟨exports, -, hex, -, hmod, -⟩ := Silmaril.Wasm.Lime1.Execution.allocate?_inv hg hal
  have ⟨hn, hf⟩ := allocExports_funcNames (Silmaril.Wasm.Lime1.Execution.mapM_forall₂ hex)
  have hpe : p.module.exports = exports := by rw [hmod]
  have hnd : (exports.map (·.name)).Nodup := by
    rw [hn]; exact hv.uniqueExports
  have hfn : funcNames exports = exps.map (·.1) := by
    rw [hf, ← hnames]
    simp only [funcExportNames, retract_exports hret]
  have hlk := lookup_funcNames hnd
  rw [hfn, ← mapM_fst] at hlk
  have h2 : exportAddrs lime1 p.module exps = some (funcAddrs exports) := by
    rw [← hlk, exportAddrs]
    simp only [Silmaril.Wasm.Component.Engine.Lime1.lime1, hpe]
    rfl
  rw [hpe]
  exact Option.some.inj (ha.symm.trans h2)

/-- The configuration of `$instantiate` for a module without start function runs `initCode`. -/
theorem instantiate_code {P : Silmaril.Wasm.Numerics.Profile} {H : Type}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} {s : Silmaril.Wasm.Execution.Core.Store H}
    {M : Silmaril.Wasm.Module} {xas : List Silmaril.Wasm.Execution.Core.ExternAddr}
    {c : Silmaril.Wasm.Execution.Core.Config H}
    (h : Silmaril.Wasm.Execution.Core.Instantiate P host s M xas c) (hs : M.start = none) :
    c = ⟨c.store, c.frame, Silmaril.Wasm.Instantiation.initCode M⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h.run
  simp only [hs, List.append_nil, Silmaril.Wasm.Instantiation.initCode]

/-- The image of the empty Lime1 store is the store of no imports. -/
theorem empty_toCore :
    Silmaril.Wasm.Execution.Runtime.Store.toCore ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) =
      Silmaril.Wasm.Game.importStore [] := rfl

/-- The executable instantiation of a global-free module from no imports is the Core 3.0
store and frame of `prepare_coreP` run at a deterministic profile (part (a)). -/
theorem instantiateDirect_core {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid l)
    (hok : ∃ xtE, Silmaril.Wasm.Validation.ModuleOk M ⟨[], xtE⟩) (hst : M.start = none)
    (bounds : Silmaril.Wasm.Lime1.Execution.InstantiationBounds
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) l)
    {p : Prepared Nat} (hp : Silmaril.Wasm.Lime1.Execution.prepare? {} l [] = some p) :
    ∃ (S : Silmaril.Wasm.Execution.Core.Store Nat) (F : Silmaril.Wasm.Execution.Core.Frame),
      Silmaril.Wasm.Execution.Core.instantiateDirect? (Silmaril.Wasm.Game.importStore []) M [] =
        some (S, F, none) ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = p.store.toCore ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInstSim p.module F.module := by
  obtain ⟨xtE, hok⟩ := hok
  have hes : M.elems.map funcrefElem = l.toCore.elems := (retract_elems hret).symm
  have hvalid : ∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk (withElems l M.elems) ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk
        (Silmaril.Wasm.Execution.Runtime.Store.toCore ({} : Silmaril.Wasm.Lime1.Execution.Store Nat)))
        (([] : List Silmaril.Wasm.Execution.Runtime.ExternVal).map
          Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) xtI := by
    rw [withElems_retract hret]; exact ⟨xtE, [], hok, .nil⟩
  obtain ⟨c₀, S, hI, hR, hS, hsim, -⟩ := prepare_coreP (P := Silmaril.Wasm.SingleThreaded.profile
    (fun _ _ _ _ => false)) (tgt := Silmaril.Wasm.SingleThreaded.Det.noHost) hes hvalid bounds hv hp
  have hI' : Silmaril.Wasm.Execution.Core.Instantiate
      (Silmaril.Wasm.SingleThreaded.profile (fun _ _ _ _ => false))
      Silmaril.Wasm.SingleThreaded.Det.noHost (Silmaril.Wasm.Game.importStore []) M [] c₀ := by
    rw [← withElems_retract hret, ← empty_toCore]; exact hI
  have hsc : Silmaril.Wasm.Lime1.Execution.startCode l.toCore = [] := by
    simp only [Silmaril.Wasm.Lime1.Execution.startCode, congrArg Silmaril.Wasm.Module.start hret,
      funcrefElems, hst]
  have hR' : Silmaril.Wasm.Execution.Core.Steps
      (Silmaril.Wasm.SingleThreaded.profile (fun _ _ _ _ => false))
      Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨c₀.store, c₀.frame, Silmaril.Wasm.Instantiation.initCode M⟩ ⟨S, c₀.frame, []⟩ := by
    rw [← instantiate_code hI' hst, ← hsc]; exact hR
  have hdir := Silmaril.Wasm.Instantiation.instantiateDirect?_complete hI' hR'
  rw [hst] at hdir
  exact ⟨S, c₀.frame, hdir, hS, hsim⟩

/-- The export addresses of the engine instance are allocated and are those of the Core
instance, given the export instances on both sides. -/
theorem exportsSim {I : EInstance lime1} {I' : Silmaril.Wasm.Game.ScalarInstance}
    {E : List Silmaril.Wasm.Execution.Runtime.ExportInst} (hA : I.addrs = funcAddrs E)
    (hA' : I'.addrs = (funcAddrs E).map (·.value))
    (hlen : I'.store.funcs.length = I.store.funcs.length)
    (hty : ∀ (k a : Nat), I'.addrs[k]? = some a → a < I'.store.funcs.length) :
    ∀ (k : Nat) (a : Silmaril.Wasm.Execution.Runtime.FuncAddr), I.addrs[k]? = some a →
      a.value < I.store.funcs.length ∧ I'.addrs.getD k 0 = a.value := by
  intro k a hk
  have hk' : I'.addrs[k]? = some a.value := by
    rw [hA', List.getElem?_map, ← hA, hk]; rfl
  exact ⟨hlen ▸ hty k _ hk', by rw [List.getD_eq_getElem?_getD, hk']; rfl⟩

/-- **The instantiation bridge for modules without globals** (parts (a) and (b)). -/
theorem instBridgeE_noGlobals (c : Simple) (hD : Lime1Dom c) (hi : c.Inst)
    (hg : c.mod.mod.globals = []) (I : EInstance lime1)
    (hI : instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I) :
    ∃ I' : Silmaril.Wasm.Game.ScalarInstance, c.mod.IsInst I' ∧ InstSim I I' := by
  obtain ⟨l, hl, hv⟩ := hD
  have hret : l.toCore = funcrefElems c.mod.mod := module_retract hl
  have hofl : ofCoreL c.mod.mod = l := by simp only [ofCoreL, hl, Option.getD_some]
  obtain ⟨I', ⟨mt, hIs⟩, himp, hexp⟩ := hi.inst
  obtain ⟨hmt, hMimp⟩ := isInst_imports hIs himp
  have hlimp : l.imports = [] := by
    simpa only [hMimp, List.map_eq_nil_iff] using retract_imports hret
  have hlg : l.globals = [] := by simpa only [hg, List.map_eq_nil_iff] using retract_globals hret
  have hI0 : instOf lime1 l [] c.mod.exports = some I := hofl ▸ hI
  obtain ⟨p, hp, hpa, hIst⟩ := instOf_inv hI0
  obtain ⟨f, hinst, haddrs⟩ := hIs.instantiated
  have hdir : Silmaril.Wasm.Execution.Core.instantiateDirect? (Silmaril.Wasm.Game.importStore [])
      c.mod.mod [] = some (I'.store, f, none) := by
    rw [← Silmaril.Wasm.Execution.Core.instantiateOnce?_of_nil hg]
    simpa only [hmt, Silmaril.Wasm.Validation.CExternType.funcs, List.length_nil, List.range_zero,
      List.map_nil] using hinst
  have hok : Silmaril.Wasm.Validation.ModuleOk c.mod.mod ⟨[], mt.exports⟩ := by
    have h := Silmaril.Wasm.Validation.validate?_sound hIs.valid
    rwa [show mt = ⟨mt.imports, mt.exports⟩ from rfl, hmt] at h
  have hst : c.mod.mod.start = none := (Silmaril.Wasm.Execution.Core.instantiateDirect?_start hdir).symm
  obtain ⟨c₁, -, -, hI₁, -⟩ := Silmaril.Wasm.Execution.Core.instantiateDirect?_sound
    (P := Silmaril.Wasm.Numerics.Profile.spec) (host := Silmaril.Wasm.SingleThreaded.Det.noHost) hdir
    ⟨_, [], hok, .nil⟩
  have bounds := bounds_of hret hg hI₁.bounded
  obtain ⟨S, F, hdir', hS, hsim⟩ := instantiateDirect_core hret hv ⟨_, hok⟩ hst bounds hp
  have heq : (I'.store, f, (none : Option Silmaril.Wasm.FuncIdx)) = (S, F, none) :=
    Option.some.inj (hdir.symm.trans hdir')
  have hSI : I'.store = S := congrArg Prod.fst heq
  have hfF : f = F := congrArg (fun x => x.2.1) heq
  have hwf : Silmaril.Wasm.Lime1.Execution.StoreWF p.store := by
    have himports : Silmaril.Wasm.Lime1.Execution.ImportsMatch ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) l [] := by
      unfold Silmaril.Wasm.Lime1.Execution.ImportsMatch; rw [hlimp]; exact .nil
    exact (Silmaril.Wasm.Lime1.Execution.prepare_wf bounds hv himports hp).1
  have hA := exportAddrs_eq hret hv hlg hp hi.names hpa
  have hex : F.module.exports = p.module.exports.map fun e => ⟨e.name, e.value.toCore⟩ :=
    congrArg Silmaril.Wasm.Execution.Core.ModuleInst.exports hsim
  have hA' : I'.addrs = (funcAddrs p.module.exports).map (·.value) := by
    rw [← haddrs, hfF]; exact exportFuncAddrs_of_exports hex
  have hlen : I'.store.funcs.length = I.store.funcs.length := by
    have h := congrArg (fun s => s.funcs.length) hS
    simpa only [Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase,
      Silmaril.Wasm.Execution.Runtime.Store.toCore, List.length_map, ← hSI, ← hIst] using h
  have hty : ∀ (k a : Nat), I'.addrs[k]? = some a → a < I'.store.funcs.length := fun k a hk => by
    obtain ⟨_, -, fi, hfi, -⟩ := Silmaril.Wasm.Lime1.Execution.forall₂_getElem? hIs.exportTypes hk
    exact (List.getElem?_eq_some_iff.mp hfi).1
  refine ⟨I', ⟨⟨mt, hIs⟩, himp, hexp⟩, hIst ▸ hwf, ?_, exportsSim hA hA' hlen hty⟩
  rw [hSI, hIst]; exact hS

end Silmaril.Proofs.Wasm.Component.Lime1Inst
