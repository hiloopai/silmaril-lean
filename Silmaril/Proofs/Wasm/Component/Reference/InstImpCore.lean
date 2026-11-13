module

public import Silmaril.Proofs.Wasm.Component.Reference.InstRun

/-!
# The core instance of `SimpleI.toRef`

The `canon lower` definitions of `SimpleI.toRef` allocate one trampoline per component import
in the empty core store (`trampStore`: function `k` has the flat type of import `k` and the host
code `.lowered ⟨k⟩ (witFt ft) {} ⟨0⟩`). For a component wired as the reference translation
assumes (`SimpleI.Inst`):

* `coreType_lowered`: the core type `canon lower` gives a trampoline is the flat type of the
  import (within the flat arities);
* `trampStore_mapH`: renamed by `trampIdx`, the trampoline store is the store of fresh host
  functions of the game semantics (`importStore`);
* `hostsSat_instantiateOnce`: instantiation adds no host code (every host function of the
  result satisfies what the host functions of the start store satisfy), proved by renaming
  the host code along a classical filter and comparing (`instantiateOnce?_mapH`);
* `coreFactsI`: the core module instantiates in the trampoline store through `prepare?` of
  `core3P P`, with the store of the instance up to `trampIdx`, only trampoline host code
  (`SimpleI.TrampOk`), and the core exports found by name.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## Instantiation adds no host code -/

section Hosts

variable {H : Type}

/-- Every host function of `s` has host code satisfying `Q`. -/
def HostsSat (Q : H → Prop) (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (h : H), s.funcs[a]? = some fi → fi.code = .host h → Q h

open Classical in
/-- Keep the host code satisfying `Q`, forget the rest. -/
noncomputable def keepIf (Q : H → Prop) (h : H) : Option H := if Q h then some h else none

theorem mapH_keepIf {Q : H → Prop} {s : Store H} (hs : HostsSat Q s) :
    Store.mapH (keepIf Q) s = Store.mapH some s := by
  have hf : s.funcs.map (FuncInst.mapH (keepIf Q)) = s.funcs.map (FuncInst.mapH some) := by
    refine List.map_congr_left fun fi hfi => ?_
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
    cases hc : fi.code with
    | wasm f => simp only [FuncInst.mapH, FuncCode.mapH, hc]
    | host h =>
      have hq : Q h := hs a fi h ha hc
      simp only [FuncInst.mapH, FuncCode.mapH, hc, keepIf, hq, ite_true]
  simp only [Store.mapH, hf]

/-- **Instantiation adds no host code**: a property of every host function of the start store
holds of every host function of the instantiated store. -/
theorem hostsSat_instantiateOnce {Q : H → Prop} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f : Frame} {st : Option FuncIdx} (hs : HostsSat Q s)
    (h : instantiateOnce? s m xas = some (s', f, st)) : HostsSat Q s' := by
  have e₁ : instantiateOnce? (Store.mapH (keepIf Q) s) m xas =
      some (Store.mapH (keepIf Q) s', f, st) := by
    rw [instantiateOnce?_mapH, h]
    rfl
  have e₂ : instantiateOnce? (Store.mapH some s) m xas = some (Store.mapH some s', f, st) := by
    rw [instantiateOnce?_mapH, h]
    rfl
  have e : Store.mapH (keepIf Q) s' = Store.mapH some s' := by
    rw [mapH_keepIf hs] at e₁
    exact (Prod.mk.inj (Option.some.inj (e₁.symm.trans e₂))).1
  intro a fi hh ha hc
  have h₁ : (Store.mapH (keepIf Q) s').funcs[a]? = (Store.mapH some s').funcs[a]? := by rw [e]
  have h₂ : FuncInst.mapH (keepIf Q) fi = FuncInst.mapH some fi := by
    simpa only [Store.mapH_funcs_getElem?, ha, Option.map_some, Option.some.injEq] using h₁
  have h₃ : keepIf Q hh = some hh := by
    have hcode := congrArg FuncInst.code h₂
    simpa only [FuncInst.mapH, FuncCode.mapH, hc, FuncCode.host.injEq] using hcode
  by_contra hq
  simp only [keepIf, hq, ite_false, reduceCtorEq] at h₃

end Hosts

/-! ## The core type of a trampoline -/

section CoreType

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.ABI

theorem head_toList_toClosed {ts : List ValTy} (h : ts.length ≤ 1) :
    (toClosedList ts).head?.toList = toClosedList ts := by
  match ts, h with
  | [], _ => rfl
  | [t], _ => rfl

/-- **The core type of a `canon lower` trampoline** without options is the flat type of the
lowered import, within the flat arities of a synchronous lower. -/
theorem coreType_lowered {E : Engine.CoreEngine} (at_ : AddrTypes E) (f : FuncId) (ft : FuncTy)
    (i : InstId) (hp : (ValTy.flatList ft.params).length ≤ 16)
    (hr : (ValTy.flatList ft.results).length ≤ 1) (hn : ft.results.length ≤ 1) :
    CanonHost.coreType at_ (.lowered f (witFt ft) {} i) = ⟨ft.flat.params, ft.flat.results⟩ := by
  have hps : (labels "a" (toClosedList ft.params)).map Prod.snd = toClosedList ft.params :=
    labels_map_snd "a" _
  have hrs : (toClosedList ft.results).head?.toList = toClosedList ft.results :=
    head_toList_toClosed hn
  have hfp : flattenTypes Silmaril.Wasm.AddrType.i32 (toClosedList ft.params) =
      ValTy.flatList ft.params := flattenTypes_toClosed _ _
  have hfr : flattenTypes Silmaril.Wasm.AddrType.i32 (toClosedList ft.results) =
      ValTy.flatList ft.results := flattenTypes_toClosed _ _
  have hfit : fitParams maxFlatParams Silmaril.Wasm.AddrType.i32 (ValTy.flatList ft.params) =
      ValTy.flatList ft.params := by
    simp only [fitParams, maxFlatParams, hp, ite_true]
  have hle : (ValTy.flatList ft.results).length ≤ maxFlatResults := hr
  simp only [CanonHost.coreType, CanonOpts.abiOptions, CanonOpts.ptrType, witFt, FuncType.ofWIT,
    hps, hrs, flattenFunc, hfp, hfr, hfit, hle, Bool.not_false, ite_true]
  rfl

end CoreType

/-! ## The trampoline store -/

section Tramp

open Silmaril.Wasm.Component.Runtime

variable {P : Profile}

/-- The flat function type of a component function type. -/
def flatV1 (ft : FuncTy) : V1.FuncType := ⟨ft.flat.params, ft.flat.results⟩

/-- The trampoline of import `k` (of type `p.2`). -/
noncomputable def trampFI (P : Profile) (k : Nat) (p : String × FuncTy) :
    FuncInst (CanonHost (core3P P)) :=
  ⟨SingleThreaded.ofFlatType (flatV1 p.2), {}, .host (.lowered ⟨k⟩ (witFt p.2) {} ⟨0⟩)⟩

/-- The core store holding the trampolines of the imports `ims`. -/
noncomputable def trampStore (P : Profile) (ims : Iface) : Store (CanonHost (core3P P)) :=
  { funcs := ims.mapIdx (trampFI P) }

theorem trampStore_funcs_mapH (ims : Iface) :
    (ims.mapIdx (trampFI P)).map (FuncInst.mapH trampIdx) =
      (ims.map fun p => SingleThreaded.ofFlatType (flatV1 p.2)).mapIdx
        fun j d => ({ type := d, module := {}, code := .host j } : FuncInst Nat) := by
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases ims[i]? with
  | none => rfl
  | some p => rfl

/-- **Renamed by `trampIdx`, the trampoline store is the store of fresh host functions** of
the flat import types. -/
theorem trampStore_mapH (ims : Iface) :
    Store.mapH trampIdx (trampStore P ims) =
      Silmaril.Wasm.Game.importStore (ims.map fun p => SingleThreaded.ofFlatType (flatV1 p.2)) := by
  simp only [Store.mapH, trampStore, Silmaril.Wasm.Game.importStore, trampStore_funcs_mapH]

theorem funcs_map_func (ds : List Validation.DefType) :
    Validation.CExternType.funcs (ds.map .func) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons, Validation.CExternType.funcs, ih]

theorem trampStore_getElem? (ims : Iface) (a : Nat) :
    (trampStore P ims).funcs[a]? = ims[a]?.map (trampFI P a) := by
  simp only [trampStore, List.getElem?_mapIdx]

/-- The host functions of the trampoline store are trampolines of the imports. -/
theorem trampStore_hosts {c : SimpleI} :
    HostsSat (fun h => ∃ (k : Nat) (hk : k < c.imports.length),
      h = .lowered ⟨k⟩ (witFt c.imports[k].2) {} ⟨0⟩) (trampStore P c.imports) := by
  intro a fi h ha hc
  rw [trampStore_getElem?] at ha
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨hk, hpk⟩ := List.getElem?_eq_some_iff.1 hp
  have hh : FuncCode.host h = FuncCode.host (.lowered ⟨a⟩ (witFt p.2) {} ⟨0⟩) := hc.symm
  refine ⟨a, hk, ?_⟩
  rw [FuncCode.host.injEq] at hh
  rw [hh, hpk]

end Tramp

/-! ## External address checks -/

section Extern

open Validation

theorem externAddrOk_self {H : Type} {s : Store H} {a : Nat} {fi : FuncInst H}
    (hs : s.funcs[a]? = some fi) (hok : ExternTypeOk {} (.func fi.type)) :
    externAddrOk? s (.func a) (.func fi.type) = true := by
  have hc : ExternTypeOk.check {} (.func fi.type) = true :=
    ExternTypeOk.check_complete (tyOk_check_complete_all {} TypeCtx.ok_empty rfl) hok
  have hx : ExternSub.check {} (.func fi.type) (.func fi.type) = true :=
    ExternSub.check_complete TypeCtx.ok_empty rfl hok hok (ExternSub.refl _ _)
  simp only [externAddrOk?, externAddrType?, hs, Option.map_some, hc, hx, Bool.and_self]

/-- The functions `k, k + 1, …` of a store whose types are the valid function types `ds` pass
the external address check against `ds`. -/
theorem externAddrsOk_range {H : Type} {s : Store H} :
    ∀ (ds : List DefType) (k : Nat), (∀ d ∈ ds, ExternTypeOk {} (.func d)) →
      (∀ i (hi : i < ds.length), ∃ fi, s.funcs[k + i]? = some fi ∧ fi.type = ds[i]) →
      externAddrsOk? s ((List.range' k ds.length).map ExternAddr.func) (ds.map .func) = true
  | [], _, _, _ => rfl
  | d :: ds, k, hok, hs => by
    obtain ⟨fi, hfi, hty⟩ := hs 0 (Nat.zero_lt_succ _)
    have hd : (d :: ds)[0] = d := rfl
    rw [hd] at hty
    rw [Nat.add_zero] at hfi
    have h₁ : externAddrOk? s (.func k) (.func d) = true := by
      rw [← hty]
      exact externAddrOk_self hfi (hty ▸ hok d List.mem_cons_self)
    have h₂ := externAddrsOk_range ds (k + 1) (fun d' hd' => hok d' (List.mem_cons_of_mem _ hd'))
      (fun i hi => by
        obtain ⟨fi', h', ht'⟩ := hs (i + 1) (Nat.succ_lt_succ hi)
        exact ⟨fi', by rw [← h', Nat.add_assoc, Nat.add_comm 1 i], ht'⟩)
    simp only [List.length_cons, List.range'_succ, List.map_cons, externAddrsOk?,
      h₁, Bool.true_and]
    exact h₂

end Extern

/-! ## Lists -/

theorem mapM_eq_some_of_getElem {α β : Type} {F : α → Option β} :
    ∀ {l : List α} {r : List β} (hl : l.length = r.length),
      (∀ i (hi : i < l.length), F l[i] = some (r[i]'(hl ▸ hi))) → l.mapM F = some r
  | [], [], _, _ => rfl
  | a :: l, b :: r, hl, h => by
    have h₀ : F a = some b := h 0 (Nat.zero_lt_succ _)
    have ht : l.mapM F = some r := mapM_eq_some_of_getElem (Nat.succ.inj hl)
      (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
    simp only [List.mapM_cons, h₀, ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-- Looking up the name of the `j`-th element of a list with distinct names, among the names
paired with values indexed from `n`, finds value `n + j`. -/
theorem lookup_mapIdx_val {α β : Type} (name : α → String) (val : Nat → β) :
    ∀ (n : Nat) (xs : List α) (j : Nat) (hj : j < xs.length), (xs.map name).Nodup →
      (xs.mapIdx fun i x => (name x, val (n + i))).lookup (name xs[j]) = some (val (n + j))
  | _, [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n, x :: xs, 0, _, _ => by simp
  | n, x :: xs, j + 1, hj, hn => by
    have hn' : name x ∉ xs.map name ∧ (xs.map name).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using hn
    have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
    have hne : (name xs[j] == name x) = false := by
      refine beq_false_of_ne fun e => hn'.1 ?_
      exact e ▸ List.mem_map_of_mem (List.getElem_mem hj')
    have ih := lookup_mapIdx_val name val (n + 1) xs j hj' hn'.2
    have hf : (fun i x => (name x, val (n + (i + 1)))) = fun i x => (name x, val (n + 1 + i)) := by
      funext i x
      rw [Nat.add_right_comm, Nat.add_assoc]
    rw [List.mapIdx_cons, List.getElem_cons_succ, List.lookup_cons, hne, hf, ih,
      Nat.add_right_comm, Nat.add_assoc]

/-! ## Exports of a single instantiation, in any store -/

/-- **The core export named by export `k` of the interface is the instance's function
`addrs.getD k 0`**, for a module instantiated in any store. -/
theorem lookup_funcExport_gen {H : Type} {m : Module} {exports : CoreIface}
    (hnames : Silmaril.Wasm.Component.Reference.funcExportNames m = exports.map (·.1))
    {mt : Validation.CModuleType} {f' : Frame} {s cs : Store H} {xas : List ExternAddr}
    {st : Option FuncIdx} {addrs : List Nat} (hv : Validation.validate? m = some mt)
    (ho : instantiateOnce? s m xas = some (cs, f', st))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = addrs) {k : Nat} {n : String}
    {ft : CoreFuncTy} (hk : exports[k]? = some (n, ft)) :
    (f'.module.exports.map fun x => (x.name, x.addr)).lookup n =
      some (.func (addrs.getD k 0)) := by
  obtain ⟨ei, hX⟩ := instantiateOnce?_exports ho
  obtain ⟨hnm, hfn⟩ := allocExports_names hX
  have hnd : (f'.module.exports.map (·.name)).Nodup := by
    rw [hnm]
    obtain ⟨⟩ := Validation.validate?_sound hv
    assumption
  have hk' : ((funcPairs f'.module.exports).map Prod.fst)[k]? = some n := by
    rw [hfn]
    change (Silmaril.Wasm.Component.Reference.funcExportNames m)[k]? = some n
    rw [hnames, List.getElem?_map, hk]
    rfl
  obtain ⟨p, hp, hpn⟩ := Option.map_eq_some_iff.1 (List.getElem?_map ▸ hk')
  have hpa : addrs[k]? = some p.2 := by
    have he : Silmaril.Wasm.Game.exportFuncAddrs f'.module =
        (funcPairs f'.module.exports).map Prod.snd := (funcPairs_snd _).symm
    rw [← ha, he, List.getElem?_map, hp]
    rfl
  have hp' : (funcPairs f'.module.exports)[k]? = some (n, p.2) := by
    rw [hp]
    exact congrArg some (Prod.ext hpn rfl)
  rw [List.getD_eq_getElem?_getD, hpa, Option.getD_some]
  exact lookup_of_funcPairs hnd hp'

/-! ## The core facts of `SimpleI.Inst` -/

section Facts

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Instantiate

variable {Pf : Profile}

/-- The flat types of the imports, as defined types. -/
noncomputable def importDefTypes (ims : Iface) : List Validation.DefType :=
  ims.map fun p => SingleThreaded.ofFlatType (flatV1 p.2)

/-- The core exports of the inline core instance of `SimpleI.toRef`: the trampolines `k` under
the names of the module's imports. -/
def envExports (ps : CoreIface) : List (String × ExternAddr) :=
  ps.mapIdx fun k p => (p.1, ExternAddr.func k)

/-- The name of the core export lifted by `x`. -/
def coreNameI (c : SimpleI) (x : SimpleExport) : String :=
  ((c.mod.exports[x.core]?).map (·.1)).getD ""

/-- The core facts of a `SimpleI.Inst` component, over `core3P Pf`: the instance, its store up
to `trampIdx` and with trampoline host code only, the core instantiation in the trampoline
store, its import vector, and the core exports found by name. -/
structure CoreFactsI (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (ci : (core3P Pf).Inst) : Prop where
  isInst : c.mod.IsInst I
  store : Store.mapH trampIdx cs = I.store
  tramp : c.TrampOk cs
  prepare : (core3P Pf).prepare? (trampStore Pf c.imports) c.mod.mod
    ((List.range c.imports.length).map ExternAddr.func) = some (cs, ci, none)
  imports : ∀ f : Frame (core3P Pf), f.coreInstance? 0 = some (envExports c.mod.imports) →
    coreImportsFor? (trampStore Pf c.imports) c.mod.mod [("env", 0)] f =
      some ((List.range c.imports.length).map ExternAddr.func)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3P Pf).exports ci) (coreNameI c x) =
    some (.func (I.addrs.getD x.core 0))

theorem importDefTypes_length (ims : Iface) : (importDefTypes ims).length = ims.length :=
  List.length_map _

theorem trampStore_type (ims : Iface) (i : Nat) (hi : i < (importDefTypes ims).length) :
    ∃ fi, (trampStore Pf ims).funcs[0 + i]? = some fi ∧ fi.type = (importDefTypes ims)[i] := by
  have hi' : i < ims.length := importDefTypes_length ims ▸ hi
  refine ⟨trampFI Pf i ims[i], ?_, ?_⟩
  · rw [Nat.zero_add, trampStore_getElem?, List.getElem?_eq_getElem hi']
    rfl
  · simp only [importDefTypes, List.getElem_map]
    rfl

/-- The validated import types of a `SimpleI.Inst` module. -/
theorem inst_importTypes {c : SimpleI} (hi : c.Inst) {mt : Validation.CModuleType}
    (hv : Validation.validate? c.mod.mod = some mt) :
    mt.imports = (importDefTypes c.imports).map .func := by
  obtain ⟨mt', hv', hmt'⟩ := hi.importTypes
  have he : mt' = mt := Option.some.inj (hv'.symm.trans hv)
  rw [← he, hmt', importDefTypes, List.map_map]
  rfl

theorem externAddrsOk_tramp {c : SimpleI} (hi : c.Inst) {mt : Validation.CModuleType}
    (hv : Validation.validate? c.mod.mod = some mt) :
    externAddrsOk? (trampStore Pf c.imports)
      ((List.range c.imports.length).map ExternAddr.func) mt.imports = true := by
  have hmt := inst_importTypes hi hv
  have hok : ∀ d ∈ importDefTypes c.imports, Validation.ExternTypeOk {} (.func d) :=
    fun d hd => Silmaril.Wasm.Component.Engine.Core3.validate?_imports_externTypeOk hv _ (hmt ▸ List.mem_map_of_mem hd)
  have h := externAddrsOk_range (s := trampStore Pf c.imports) (importDefTypes c.imports) 0 hok
    (trampStore_type c.imports)
  rw [importDefTypes_length, ← List.range_eq_range'] at h
  rw [hmt]
  exact h

/-- The import list of the engine on a module of type `mt`. -/
def importTypesOf (m : Module) {mt : Validation.CModuleType}
    (hv : Validation.validate? m = some mt) : List (String × String × Core3.ExtT) :=
  (m.imports.zip (mt.imports.attachWith _
    (Silmaril.Wasm.Component.Engine.Core3.validate?_imports_externTypeOk hv))).map
    fun p => (p.1.moduleName, p.1.name, p.2)

theorem importTypesE_eq {m : Module} {mt : Validation.CModuleType}
    (hv : Validation.validate? m = some mt) : Core3.importTypesE m = importTypesOf m hv := by
  unfold Core3.importTypesE
  split
  next mt' hv' =>
    have he : mt' = mt := Option.some.inj (hv'.symm.trans hv)
    subst he
    rfl
  next hv' => exact absurd hv (by rw [hv']; exact fun h => by cases h)

/-- The import types of the engine on a `SimpleI.Inst` module: import `i` is
`"env" "name_i"` at the flat type of import `i`. -/
theorem importTypesE_getElem {c : SimpleI} (hi : c.Inst) :
    (Core3.importTypesE c.mod.mod).length = c.imports.length ∧
      ∀ i (h₁ : i < (Core3.importTypesE c.mod.mod).length) (h₂ : i < c.imports.length),
        (Core3.importTypesE c.mod.mod)[i].1 = "env" ∧
        (Core3.importTypesE c.mod.mod)[i].2.1 = c.imports[i].1 ∧
        (Core3.importTypesE c.mod.mod)[i].2.2.val = .func ((importDefTypes c.imports)[i]'(by
          rw [importDefTypes_length]; exact h₂)) := by
  obtain ⟨I, ⟨mt, hIs⟩, -⟩ := hi.inst
  have hv := hIs.valid
  have hlen : c.mod.mod.imports.length = c.imports.length := by
    simpa only [List.length_map] using congrArg List.length hi.env
  have hmt := inst_importTypes hi hv
  have hlen' : mt.imports.length = c.imports.length := by
    rw [hmt, List.length_map, importDefTypes_length]
  rw [importTypesE_eq hv]
  refine ⟨by simp [importTypesOf, hlen, hlen'], fun i h₁ h₂ => ?_⟩
  have hil : i < c.mod.mod.imports.length := hlen ▸ h₂
  have he : (c.mod.mod.imports[i].moduleName, c.mod.mod.imports[i].name) =
      ("env", c.imports[i].1) := by
    have := congrArg (fun l => l[i]?) hi.env
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hil,
      List.getElem?_eq_getElem h₂, Option.map_some, Option.some.injEq] using this
  have hty : mt.imports[i]'(hlen' ▸ h₂) = .func ((importDefTypes c.imports)[i]'(by
      rw [importDefTypes_length]; exact h₂)) := by
    simp only [hmt, List.getElem_map]
  simp only [importTypesOf, List.getElem_map, List.getElem_zip, List.getElem_attachWith]
  exact ⟨(Prod.mk.inj he).1, (Prod.mk.inj he).2, hty⟩

theorem externTypeE_tramp {c : SimpleI} (hi : c.Inst) (i : Nat) (hi' : i < c.imports.length) :
    ∃ h, Core3.externTypeE? (trampStore Pf c.imports) (.func i) =
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
  obtain ⟨fi, hfi, hty⟩ := trampStore_type (Pf := Pf) c.imports i hil
  rw [Nat.zero_add] at hfi
  refine ⟨Validation.ExternTypeOk.check_sound hc, ?_⟩
  simp only [Core3.externTypeE?, externAddrType?, hfi, Option.map_some, hty, hc, dite_true]

/-- **The import vector of the core instantiation** in the trampoline store: import `i` of the
module is the trampoline `i`, exported by the inline core instance under its name. -/
theorem coreImportsFor_tramp {c : SimpleI} (hc : c.Good) (hi : c.Inst) (fr : Frame (core3P Pf))
    (hfr : fr.coreInstance? 0 = some (envExports c.mod.imports)) :
    coreImportsFor? (trampStore Pf c.imports) c.mod.mod [("env", 0)] fr =
      some ((List.range c.imports.length).map ExternAddr.func) := by
  obtain ⟨hlen, hT⟩ := importTypesE_getElem hi
  have hnd : (c.mod.imports.map (·.1)).Nodup := by
    rw [hc.imports, List.map_map]
    exact hi.importNames
  have hlenm : c.mod.imports.length = c.imports.length := by rw [hc.imports, List.length_map]
  show (Core3.importTypesE c.mod.mod).mapM _ = _
  refine mapM_eq_some_of_getElem
    (by rw [hlen]; exact (Eq.trans (List.length_map _) List.length_range).symm) fun i h₁ => ?_
  have h₂ : i < c.imports.length := hlen ▸ h₁
  obtain ⟨e₁, e₂, e₃⟩ := hT i h₁ h₂
  have hname : c.mod.imports[i].1 = c.imports[i].1 := by
    simp only [hc.imports, List.getElem_map]
  have hlk : lookupExport? (envExports c.mod.imports) c.imports[i].1 = some (.func i) := by
    have h := lookup_mapIdx_val (·.1) ExternAddr.func 0 c.mod.imports i (hlenm ▸ h₂) hnd
    simp only [Nat.zero_add] at h
    rw [← hname]
    exact h
  obtain ⟨hτ, hext⟩ := externTypeE_tramp (Pf := Pf) hi i h₂
  have hsub : (core3P Pf).ExternSub ⟨_, hτ⟩ (Core3.importTypesE c.mod.mod)[i].2.2 := by
    show Validation.ExternSub {} _ (Core3.importTypesE c.mod.mod)[i].2.2.val
    rw [e₃]
    exact Validation.ExternSub.refl _ _
  have hget : ((List.range c.imports.length).map ExternAddr.func)[i]'(by
      rw [List.length_map, List.length_range]; exact h₂) = .func i := by
    simp only [List.getElem_map, List.getElem_range]
  refine Eq.trans ?_ (congrArg some hget.symm)
  simp only [coreImportFor?, e₁, e₂, List.lookup_cons, beq_self_eq_true, Option.bind_eq_bind,
    Option.bind_some, hfr]
  have hext' : (core3P Pf).externType? (trampStore Pf c.imports) (ExternAddr.func i) =
      some ⟨_, hτ⟩ := hext
  erw [Option.bind_some, hlk, Option.bind_some, hext', Option.bind_some]
  simp only [hsub, ↓reduceIte]


/-- **The core facts hold** for a `SimpleI.Inst` component in the fragment. -/
theorem coreFactsI {c : SimpleI} (hc : c.Good) (hi : c.Inst) :
    ∃ I cs ci, CoreFactsI (Pf := Pf) c I cs ci := by
  obtain ⟨I, hI⟩ := hi.inst
  obtain ⟨⟨mt, hIs⟩, -, -⟩ := id hI
  have hmt := inst_importTypes hi hIs.valid
  have hlen : mt.imports.length = c.imports.length := by
    rw [hmt, List.length_map, importDefTypes_length]
  have hfuncs : Validation.CExternType.funcs mt.imports = importDefTypes c.imports := by
    rw [hmt, funcs_map_func]
  obtain ⟨f, hf, haddr⟩ := hIs.instantiated
  have hf' : mapS trampIdx (instantiateOnce? (trampStore Pf c.imports) c.mod.mod
      ((List.range c.imports.length).map ExternAddr.func)) = some (I.store, f, none) := by
    rw [← instantiateOnce?_mapH, trampStore_mapH, ← hlen]
    rw [hfuncs] at hf
    exact hf
  obtain ⟨cs, ho, hs⟩ := mapS_eq_some hf'
  have hprep : (core3P Pf).prepare? (trampStore Pf c.imports) c.mod.mod
      ((List.range c.imports.length).map ExternAddr.func) = some (cs, f.module, none) := by
    show Core3.prepareE? _ _ _ = _
    simp only [Core3.prepareE?, hIs.valid]
    split
    · erw [ho]
      rfl
    · exact absurd (externAddrsOk_tramp (Pf := Pf) hi hIs.valid) ‹_›
  refine ⟨I, cs, f.module, ⟨hI, hs, hostsSat_instantiateOnce trampStore_hosts ho, hprep,
    fun fr hfr => ?_, fun x hx => ?_⟩⟩
  · exact coreImportsFor_tramp hc hi fr hfr
  · obtain ⟨n, hn⟩ := hc.core x hx
    have hname : coreNameI c x = n := by rw [coreNameI, hn]; rfl
    rw [hname]
    exact lookup_funcExport_gen hi.names hIs.valid ho haddr hn

end Facts

end Silmaril.Proofs.Wasm.Component.Reference
