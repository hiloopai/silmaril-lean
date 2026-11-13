module

public import Silmaril.Proofs.Wasm.Component.Reference.Phases
public import Silmaril.Wasm.Game.Instantiate.Defs

/-!
# The core instance of `Simple.toRef`

The `core instance (instantiate 0)` definition of `Simple.toRef` instantiates the module of a
`Simple` component in the empty core store of `core3P P`. For a component whose module is
instantiated as the IR assumes (`Simple.Inst`):

* `prepare_toRef`: the engine's `prepare?` succeeds without a start function, its store is
  the instance store of the game semantics up to the host type, and the module has no imports
  (`importTypes_nil`);
* `lookup_coreExport`: the `alias core export` of the core export named
  `c.mod.exports[k].1` finds the function address `I.addrs.getD k 0` of the instance (the core
  export names are distinct by validation, `exports_nodup`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## Function exports of a module instance -/

/-- The function exports of a list of export instances, with their names. -/
def funcPairs (L : List ExportInst) : List (String × Nat) :=
  L.filterMap fun x => match x.addr with
    | .func a => some (x.name, a)
    | _ => none

theorem funcPairs_cons_func {x : ExportInst} {a : Nat} (L : List ExportInst)
    (h : x.addr = .func a) : funcPairs (x :: L) = (x.name, a) :: funcPairs L := by
  simp only [funcPairs, List.filterMap_cons, h]

theorem funcPairs_cons_other {x : ExportInst} (L : List ExportInst)
    (h : ∀ a, x.addr ≠ .func a) : funcPairs (x :: L) = funcPairs L := by
  cases hx : x.addr with
  | func a => exact absurd hx (h a)
  | _ => simp only [funcPairs, List.filterMap_cons, hx]

theorem mem_names_of_funcPairs {L : List ExportInst} {n : String} {a : Nat}
    (h : (n, a) ∈ funcPairs L) : n ∈ L.map (·.name) := by
  unfold funcPairs at h
  obtain ⟨x, hx, hxa⟩ := List.mem_filterMap.1 h
  have hn : x.name = n := by
    split at hxa
    · exact (Prod.mk.inj (Option.some.inj hxa)).1
    · cases hxa
  exact List.mem_map.2 ⟨x, hx, hn⟩

/-- The lookup of the name of a function export finds its address. -/
theorem lookup_of_funcPairs : ∀ {L : List ExportInst} {k : Nat} {n : String} {a : Nat},
    (L.map (·.name)).Nodup → (funcPairs L)[k]? = some (n, a) →
      (L.map fun x => (x.name, x.addr)).lookup n = some (.func a)
  | [], _, _, _, _, h => by simp [funcPairs] at h
  | x :: L, k, n, a, hnd, h => by
    have hnd' : x.name ∉ L.map (·.name) ∧ (L.map (·.name)).Nodup := List.nodup_cons.1 hnd
    have hskip : ∀ k' : Nat, (funcPairs L)[k']? = some (n, a) →
        ((x :: L).map fun x => (x.name, x.addr)).lookup n = some (.func a) := by
      intro k' hk'
      have hne : n ≠ x.name := fun e =>
        hnd'.1 (e ▸ mem_names_of_funcPairs (List.mem_of_getElem? hk'))
      have hbeq : (n == x.name) = false := by simpa only [beq_eq_false_iff_ne] using hne
      rw [List.map_cons, List.lookup_cons, hbeq]
      exact lookup_of_funcPairs hnd'.2 hk'
    cases hx : x.addr with
    | func a₀ =>
      rw [funcPairs_cons_func L hx] at h
      cases k with
      | zero =>
        have he : (x.name, a₀) = (n, a) := Option.some.inj h
        rw [List.map_cons, List.lookup_cons, ← (Prod.mk.inj he).1, beq_self_eq_true, hx,
          (Prod.mk.inj he).2]
      | succ k => exact hskip k h
    | _ => exact hskip k (by rwa [funcPairs_cons_other L (fun a e => by rw [hx] at e; cases e)] at h)

/-- The addresses of `funcPairs` are the exported function addresses. -/
theorem funcPairs_snd (L : List ExportInst) :
    (funcPairs L).map Prod.snd = L.filterMap fun x => match x.addr with
      | .func a => some a
      | _ => none := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    cases hx : x.addr with
    | func a =>
      rw [funcPairs_cons_func L hx, List.map_cons, ih, List.filterMap_cons, hx]
    | _ =>
      rw [funcPairs_cons_other L (fun a e => by rw [hx] at e; cases e), ih, List.filterMap_cons, hx]

/-- An allocated export keeps the name and the kind of its index. -/
theorem allocExport?_name {mi : ModuleInst} {e : Silmaril.Wasm.Export} {x : ExportInst}
    (h : allocExport? mi e = some x) :
    x.name = e.name ∧ (∀ i, e.index = .func i → ∃ a, x.addr = .func a) ∧
      ((∀ i, e.index ≠ .func i) → ∀ a, x.addr ≠ .func a) := by
  unfold allocExport? at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨rfl, fun i hi => ?_, fun hi a => ?_⟩
  · rw [hi] at hv
    obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hv
    exact ⟨b, rfl⟩
  · cases hidx : e.index with
    | func i => exact absurd hidx (hi i)
    | _ =>
      rw [hidx] at hv
      obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hv
      intro e'
      cases e'

/-- Allocated exports have the names of the module's exports, and their function exports
have the names of the module's function exports. -/
theorem allocExports_names {mi : ModuleInst} :
    ∀ {es : List Silmaril.Wasm.Export} {L : List ExportInst},
      List.Forall₂ (fun e x => allocExport? mi e = some x) es L →
      L.map (·.name) = es.map (·.name) ∧
        (funcPairs L).map Prod.fst = es.filterMap fun x => match x.index with
          | .func _ => some x.name
          | _ => none
  | [], [], .nil => ⟨rfl, rfl⟩
  | e :: es, x :: L, .cons h hs => by
    obtain ⟨hn, hf, ho⟩ := allocExport?_name h
    obtain ⟨ih₁, ih₂⟩ := allocExports_names hs
    refine ⟨by rw [List.map_cons, List.map_cons, hn, ih₁], ?_⟩
    cases hidx : e.index with
    | func i =>
      obtain ⟨a, ha⟩ := hf i hidx
      rw [funcPairs_cons_func L ha, List.map_cons, ih₂, List.filterMap_cons, hidx, hn]
    | _ =>
      rw [funcPairs_cons_other L (ho (fun i e' => by rw [hidx] at e'; cases e')), ih₂,
        List.filterMap_cons, hidx]

/-! ## Exports of a single instantiation -/

theorem mapM_forall₂ {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → List.Forall₂ (fun a b => g a = some b) l r
  | [], r, h => by
    have hr : r = [] := (Option.some.inj h).symm
    rw [hr]
    exact .nil
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (mapM_forall₂ hbs)

variable {H : Type}

/-- The exports of the module instance built by `prepare?` are allocated from the module's
exports. -/
theorem prepare?_exports {ev : Store H → Frame → Expr → Option (Store H × Execution.Core.Val)} {s : Store H}
    {m : Module} {xas : List ExternAddr} {c : Config H} {st : Option FuncIdx}
    (hp : prepare? ev s m xas = some (c, st)) :
    ∃ ei, List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports c.frame.module.exports := by
  unfold prepare? at hp
  split at hp
  · split at hp
    · cases hp
    split at hp
    · cases hp
    split at hp
    · cases hp
    split at hp
    · cases hp
    next s₄ mi hM =>
      obtain ⟨tagTypes, funcTypes, xi, -, -, hX, hmi, -⟩ := allocModule?_inv hM
      have hc : c.frame.module = mi := by rw [← (Prod.mk.inj (Option.some.inj hp)).1]
      rw [hc, hmi]
      exact ⟨_, mapM_forall₂ hX⟩
  · cases hp

/-- The exports of a module instance built by `instantiateOnce?` are allocated from the
module's exports. -/
theorem instantiateOnce?_exports {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (h : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ ei, List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports f'.module.exports := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  · obtain ⟨c, hp, hf⟩ := prepareDirect?_frame h
    rw [hf]
    exact prepare?_exports (m := m.globalResidue) hp

theorem mapS_eq_some {g : H → Nat} {o : Option (Store H × Frame × Option FuncIdx)}
    {s : Store Nat} {f : Frame} {st : Option FuncIdx} (h : mapS g o = some (s, f, st)) :
    ∃ s', o = some (s', f, st) ∧ Store.mapH g s' = s := by
  cases o with
  | none => cases h
  | some p =>
    obtain ⟨s', f', st'⟩ := p
    have he : (Store.mapH g s', f', st') = (s, f, st) := Option.some.inj h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
    exact ⟨s', rfl, h₁⟩

/-- Function imports only: no function import means no import. -/
theorem nil_of_funcs_nil : ∀ {l : List Validation.CExternType},
    (∀ xt ∈ l, ∃ d, xt = .func d) → Validation.CExternType.funcs l = [] → l = []
  | [], _, _ => rfl
  | xt :: l, hf, h => by
    obtain ⟨d, rfl⟩ := hf xt List.mem_cons_self
    cases h

/-- **The module of a `Simple.Inst` component instantiates in the empty store of any host
type**, without imports or start function, to the instance store up to the host type. -/
theorem inst_once (g : H → Nat) {c : Simple} (hi : c.Inst) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (mt : Validation.CModuleType) (cs : Store H)
      (f' : Frame), c.mod.IsInst I ∧ Validation.validate? c.mod.mod = some mt ∧
      mt.imports = [] ∧ instantiateOnce? ({} : Store H) c.mod.mod [] = some (cs, f', none) ∧
      Store.mapH g cs = I.store ∧ Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs := by
  obtain ⟨I, hI⟩ := hi.inst
  obtain ⟨⟨mt, hIs⟩, himp, -⟩ := id hI
  have hfn : Validation.CExternType.funcs mt.imports = [] :=
    List.forall₂_nil_right_iff.1 (himp ▸ hIs.importTypes)
  have hmt : mt.imports = [] := nil_of_funcs_nil hIs.funcImports hfn
  obtain ⟨f, hf, haddr⟩ := hIs.instantiated
  have hf₀ : instantiateOnce? (Silmaril.Wasm.Game.importStore []) c.mod.mod [] =
      some (I.store, f, none) := by
    rw [← hf, hmt]
    rfl
  have hf' : mapS g (instantiateOnce? ({} : Store H) c.mod.mod []) = some (I.store, f, none) := by
    rw [← instantiateOnce?_importStore g, hf₀]
  obtain ⟨cs, ho, hs⟩ := mapS_eq_some hf'
  exact ⟨I, mt, cs, f, hI, hIs.valid, hmt, ho, hs, haddr⟩

/-- **The core export named by export `k` of the interface is the instance's function
`I.addrs.getD k 0`.** -/
theorem lookup_funcExport {c : Simple} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs : Store H}
    (hv : Validation.validate? c.mod.mod = some mt)
    (ho : instantiateOnce? ({} : Store H) c.mod.mod [] = some (cs, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) {k : Nat} {n : String}
    {ft : CoreFuncTy} (hk : c.mod.exports[k]? = some (n, ft)) :
    (f'.module.exports.map fun x => (x.name, x.addr)).lookup n =
      some (.func (I.addrs.getD k 0)) := by
  obtain ⟨ei, hX⟩ := instantiateOnce?_exports ho
  obtain ⟨hnames, hfn⟩ := allocExports_names hX
  have hnd : (f'.module.exports.map (·.name)).Nodup := by
    rw [hnames]
    obtain ⟨⟩ := Validation.validate?_sound hv
    assumption
  have hk' : ((funcPairs f'.module.exports).map Prod.fst)[k]? = some n := by
    rw [hfn]
    change (funcExportNames c.mod.mod)[k]? = some n
    rw [hi.names, List.getElem?_map, hk]
    rfl
  obtain ⟨p, hp, hpn⟩ := Option.map_eq_some_iff.1 (List.getElem?_map ▸ hk')
  have hpa : I.addrs[k]? = some p.2 := by
    have he : Silmaril.Wasm.Game.exportFuncAddrs f'.module =
        (funcPairs f'.module.exports).map Prod.snd := (funcPairs_snd _).symm
    rw [← ha, he, List.getElem?_map, hp]
    rfl
  have hp' : (funcPairs f'.module.exports)[k]? = some (n, p.2) := by
    rw [hp]
    exact congrArg some (Prod.ext hpn rfl)
  rw [List.getD_eq_getElem?_getD, hpa, Option.getD_some]
  exact lookup_of_funcPairs hnd hp'

/-! ## The engine `core3P P` -/

section Engine

open Silmaril.Wasm.Component.Engine

variable (P : Profile)

/-- `prepare?` of `core3P P` on an import-free, start-free module. -/
theorem prepare_core3P {m : Module} {mt : Validation.CModuleType}
    {cs : Store (Silmaril.Wasm.Component.Runtime.CanonHost (core3P P))} {f' : Frame}
    (hv : Validation.validate? m = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (Silmaril.Wasm.Component.Runtime.CanonHost (core3P P))) m [] =
      some (cs, f', none)) :
    (core3P P).prepare? ((core3P P).empty _) m [] = some (cs, f'.module, none) := by
  show Core3.prepareE? {} m [] = _
  simp only [Core3.prepareE?, hv, hmt, ho, externAddrsOk?, ite_true]
  rfl

/-- `importTypes` of `core3P P` on an import-free module. -/
theorem importTypes_core3P {m : Module} {mt : Validation.CModuleType}
    (hv : Validation.validate? m = some mt) (hmt : mt.imports = []) :
    (core3P P).importTypes m = [] := by
  show Core3.importTypesE m = []
  unfold Core3.importTypesE
  split
  next mt' hv' =>
    have he : mt' = mt := Option.some.inj (hv'.symm.trans hv)
    subst he
    simp only [hmt, List.attachWith_nil, List.zip_nil_right, List.map_nil]
  next hv' => rfl

/-- The exports of a core instance of `core3P P`. -/
theorem exports_core3P (mi : ModuleInst) :
    (core3P P).exports mi = mi.exports.map fun x => (x.name, x.addr) := rfl

end Engine

end Silmaril.Proofs.Wasm.Component.Reference
