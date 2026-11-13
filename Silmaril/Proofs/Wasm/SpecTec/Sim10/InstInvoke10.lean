module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstHost10

/-!
# Core's `InvokeOk` from V1 data

Every form of the 1.0 forward run from instantiation still assumed Core's `InvokeOk` of the
invocation: a function at the invoked address, and arguments typed by its parameters, read in
the Core image. This module derives it from V1:

* **`invokeOk_of_v1`**: from a V1 function instance at the address and arguments whose V1
  types are its parameters. This is the precondition of the 1.0 embedder's `invoke`.
* `importFuncs_forall₂`, **`allocate?_funcs`**, **`prepare?_funcs`**: after preparation, the
  function addresses of the new module instance and the function types of the module's
  validation context (`moduleContext`, imports then definitions) correspond one for one: the
  store holds a function of exactly that type at each address. Imports are aligned through
  `ImportsMatch`; definitions through the allocation.
* `step_funcs10`, `steps_funcs10`: a V1 run from a store with no host function keeps the
  functions.
* **`instantiation_funcs`**: so the same correspondence holds in the store after a V1
  instantiation from a store with no host function.
* **`instantiation_export_invokeOk`**: for every **exported** function of the instantiated
  module, V1 validation gives the export a function type `ft` (`ExportValid`), and Core's
  `InvokeOk` holds for every argument list whose V1 types are `ft.params`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstInvoke

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps Instantiation
  prepare? allocate? importedInstance ImportsMatch ExternMatches exportValue? addresses)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal FuncInst FuncAddr ModuleInst)
open Silmaril.Wasm.V1.Validation (moduleContext exportType? importType?)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.Whole (NoHost10)
open Silmaril.Wasm.SpecTec.Sim10 (StoreOk10)

variable {H : Type}

/-! ## `InvokeOk` from V1 -/

/-- **Core's `InvokeOk` from a V1 function instance and arguments of its parameter types.** -/
theorem invokeOk_of_v1 {s : Store H} {a : FuncAddr} {fi : FuncInst V1.Func H}
    {args : List Value} (hf : s.funcs[a.value]? = some fi)
    (hty : args.map Value.type = fi.type.params) :
    Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore) := by
  have hty' : (fi.mapCode V1.Func.toLime).toCore.type = fi.type.toDefType := by
    cases fi <;> rfl
  refine ⟨(fi.mapCode V1.Func.toLime).toCore, _, _, ?_,
    Validation.Expand.iff.mpr (hty' ▸ V1.FuncType.toDefType_expand fi.type), ?_⟩
  · simp [coreStore10, Execution.Runtime.Store.toCore, Execution.Runtime.Store.mapCode, hf]
  · rw [Validation.Ty.toList_ofList, ← hty]
    clear hty
    induction args with
    | nil => exact .nil
    | cons v vs ih => exact .cons (.num _) ih

/-! ## Function addresses against the validation context -/

/-- The store holds a function of type `ft` at `a`. -/
def FuncAt (s : Store H) (ft : V1.FuncType) (a : FuncAddr) : Prop :=
  ∃ fi : FuncInst V1.Func H, s.funcs[a.value]? = some fi ∧ fi.type = ft

/-- The imported function types of a validation context. -/
def ctxImportFuncs (types : List V1.FuncType) (L : List V1.Import) : List V1.FuncType :=
  L.filterMap fun i => match i.desc with
    | .func idx => types[idx.toNat]?
    | _ => none

/-- **Imported functions are aligned with the context's imported function types.** -/
theorem importFuncs_forall₂ {s : Store H} {types : List V1.FuncType} :
    ∀ {L : List V1.Import} {imports : List ExternVal},
      List.Forall₂ (fun i e => ∃ et, importType? types i.desc = some et ∧ ExternMatches s e et)
        L imports →
      List.Forall₂ (FuncAt s) (ctxImportFuncs types L) (importedInstance imports).funcs
  | [], [], .nil => .nil
  | i :: L, e :: imports, .cons ⟨et, hit, hm⟩ hrest => by
    have ih := importFuncs_forall₂ hrest
    simp only [ctxImportFuncs, importedInstance] at ih ⊢
    rcases hd : i.desc with idx | tt | mt | gt <;> rw [hd] at hit <;>
      simp only [importType?, Option.map_eq_some_iff] at hit
    · obtain ⟨ft, hft, rfl⟩ := hit
      cases hm with
      | func a fn _ found typed =>
        simp only [List.filterMap_cons, hd, hft]
        exact .cons ⟨fn, found, typed⟩ ih
    all_goals
      cases hit
      cases hm
      simpa only [List.filterMap_cons, hd] using ih

/-- `FuncAt` survives appending functions. -/
theorem FuncAt.append {s : Store H} {ft : V1.FuncType} {a : FuncAddr} (h : FuncAt s ft a)
    (fs : List (FuncInst V1.Func H)) {s' : Store H} (he : s'.funcs = s.funcs ++ fs) :
    FuncAt s' ft a := by
  obtain ⟨fi, hf, ht⟩ := h
  refine ⟨fi, ?_, ht⟩
  rw [he, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hf).1]
  exact hf

theorem forall₂_append {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {r₁ r₂ : List β}, List.Forall₂ R l₁ r₁ → List.Forall₂ R l₂ r₂ →
      List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons hr h₁, h₂ => .cons hr (forall₂_append h₁ h₂)

theorem forall₂_imp {α β : Type _} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → List.Forall₂ S l r
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hr h => .cons (hRS _ _ hr) (forall₂_imp hRS h)

/-- Corresponding entries of `Forall₂`-related lists are related. -/
theorem forall₂_getElem? {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → ∀ {i : Nat} {x : α} {y : β},
      l[i]? = some x → r[i]? = some y → R x y
  | [], [], .nil, _, _, _, hx, _ => by simp at hx
  | a :: l, b :: r, .cons hab h, i, x, y, hx, hy => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      exact hx ▸ hy ▸ hab
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx hy
      exact forall₂_getElem? h hx hy

/-- Fresh addresses point at the appended functions, in order. -/
theorem fresh_forall₂ :
    ∀ (pre fs : List (FuncInst V1.Func H)),
      List.Forall₂ (fun ft (a : FuncAddr) => ∃ fi : FuncInst V1.Func H,
          (pre ++ fs)[a.value]? = some fi ∧ fi.type = ft)
        (fs.map FuncInst.type) (addresses .func pre.length fs.length)
  | _, [] => .nil
  | pre, fi :: fs => by
    have ih := fresh_forall₂ (pre ++ [fi]) fs
    have e : addresses .func pre.length (fi :: fs).length =
        ⟨pre.length⟩ :: addresses .func (pre ++ [fi]).length fs.length := by
      simp only [addresses, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, Nat.add_zero, List.length_append, List.length_nil]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Execution.Runtime.Addr.mk.injEq]
      omega
    rw [e, List.map_cons]
    refine .cons ⟨fi, by simp, rfl⟩ ?_
    simpa only [List.append_assoc, List.singleton_append] using ih

/-- A successful `mapM` whose results have the types `G` reads. -/
theorem filterMap_of_mapM {g : V1.Func → Option (FuncInst V1.Func H)}
    {G : V1.Func → Option V1.FuncType} (hg : ∀ f fi, g f = some fi → G f = some fi.type) :
    ∀ {l : List V1.Func} {fs : List (FuncInst V1.Func H)}, l.mapM g = some fs →
      l.filterMap G = fs.map FuncInst.type
  | [], fs, h => by simp at h; subst h; rfl
  | f :: l, fs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨fi, hfi, fs', hfs', rfl⟩ := h
    simp only [List.filterMap_cons, hg f fi hfi, List.map_cons, filterMap_of_mapM hg hfs']

/-- **After allocation, the module instance's function addresses hold functions of the
validation context's function types**, one for one. -/
theorem allocate?_funcs {s s₁ : Store H} {m : V1.Module} {imports : List ExternVal}
    {mi : ModuleInst} (hi : ImportsMatch s m imports) (h : allocate? s m imports = some (s₁, mi)) :
    List.Forall₂ (FuncAt s₁) (moduleContext m).funcs mi.funcs ∧
      ∀ x ∈ mi.exports, ∃ e ∈ m.exports, exportValue? mi e.index = some x.value := by
  unfold allocate? at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨inits, -, exps, hexps, fs, hfs, rfl, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · refine forall₂_append (forall₂_imp (fun ft a h => FuncAt.append h fs rfl)
      (importFuncs_forall₂ hi)) ?_
    have hdef := fresh_forall₂ s.funcs fs
    rw [mapM_some_length hfs] at hdef
    have hfm := filterMap_of_mapM (G := fun f => m.types[f.type.toNat]?) (fun f fi hf => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hf
      obtain ⟨ft, hft, rfl⟩ := hf
      exact hft) hfs
    rw [← hfm] at hdef
    exact hdef
  · intro x hx
    obtain ⟨e, he, hex⟩ := mapM_some_mem hexps x hx
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hex
    obtain ⟨v, hv, rfl⟩ := hex
    exact ⟨e, he, by cases hix : e.index <;> rw [hix] at hv <;> exact hv⟩

/-- Element writes keep the functions. -/
theorem foldl_applyElem_funcs : ∀ (ws : List V1.Execution.ElemWrite) (s : Store H),
    (ws.foldl V1.Execution.applyElem s).funcs = s.funcs
  | [], _ => rfl
  | w :: ws, s => foldl_applyElem_funcs ws (V1.Execution.applyElem s w)

/-- **After preparation**, the same correspondence, and the exports. -/
theorem prepare?_funcs {s : Store H} {m : V1.Module} {imports : List ExternVal}
    {p : V1.Execution.Prepared H} (hi : ImportsMatch s m imports)
    (h : prepare? s m imports = some p) :
    List.Forall₂ (FuncAt p.store) (moduleContext m).funcs p.module.funcs ∧
      ∀ x ∈ p.module.exports, ∃ e ∈ m.exports, exportValue? p.module e.index = some x.value := by
  have hmod : ∃ s₁ mi, allocate? s m imports = some (s₁, mi) ∧ p.module = mi ∧
      p.store.funcs = s₁.funcs := by
    obtain ⟨s₁, mi, elems, data, ha, -, hp⟩ := prepare_store h
    refine ⟨s₁, mi, ha, ?_, ?_⟩
    · unfold prepare? at h
      simp only [bind, Option.bind_eq_some_iff, pure, ha] at h
      obtain ⟨⟨s₂, mi₂⟩, hs₂, elems₂, -, data₂, -, hrest⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at hs₂
      obtain ⟨rfl, rfl⟩ := hs₂
      cases hm : m.start <;> simp only [hm, Option.bind_eq_some_iff, Option.some.injEq] at hrest
      · obtain ⟨_, -, rfl⟩ := hrest; rfl
      · obtain ⟨_, -, rfl⟩ := hrest; rfl
    · rw [hp, (foldl_applyData _ data).1, foldl_applyElem_funcs]
  obtain ⟨s₁, mi, ha, hm, hf⟩ := hmod
  obtain ⟨hF, hE⟩ := allocate?_funcs hi ha
  rw [hm]
  exact ⟨forall₂_imp (fun ft a ⟨fi, h₁, h₂⟩ => ⟨fi, hf ▸ h₁, h₂⟩) hF, hE⟩

/-! ## Runs keep the functions -/

/-- **A V1 step from a store with no host function keeps the functions.** -/
theorem step_funcs10 {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hnh : NoHost10 c.store) : c'.store.funcs = c.store.funcs := by
  induction h with
  | context _ vs tail ih => exact ih hnh
  | label _ n cont ih => exact ih hnh
  | frame _ n outer ih => exact ih hnh
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact absurd h₁ (hnh _ _ _)
  | _ => rfl

/-- The same along a run. -/
theorem steps_funcs10 {host : HostSemantics H} {c c' : Config H} (h : Steps host c c')
    (hnh : NoHost10 c.store) : c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail hb hs ih =>
    rw [step_funcs10 hs (fun i ft h' e => hnh i ft h' (ih ▸ e)), ih]

/-- **After a V1 instantiation from a store with no host function**, the instance's function
addresses hold functions of the validation context's types, and its exports come from the
module's. -/
theorem instantiation_funcs {host : HostSemantics H} {before after : Store H} {m : V1.Module}
    {imports : List ExternVal} {module : ModuleInst} {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hnh : NoHost10 before)
    (hs : StoreOk10 before) :
    List.Forall₂ (FuncAt after) (moduleContext m).funcs module.funcs ∧
      ∀ x ∈ module.exports, ∃ e ∈ m.exports, exportValue? module e.index = some x.value := by
  obtain ⟨p, hp, rfl, hst⟩ := hI.prepared
  have hnh' := (storeOk10_prepare hI.valid hI.importsMatch hnh hs hp).1
  have he : after.funcs = p.store.funcs := steps_funcs10 hst hnh'
  obtain ⟨hF, hE⟩ := prepare?_funcs hI.importsMatch hp
  exact ⟨forall₂_imp (fun ft a ⟨fi, h₁, h₂⟩ => ⟨fi, he ▸ h₁, h₂⟩) hF, hE⟩

/-- **Core's `InvokeOk` for an exported function, from V1 validation**: after a V1
instantiation from a store with no host function, every export of the instance that is a
function has, by validation, a function type `ft`, and `InvokeOk` holds for every argument
list whose V1 types are `ft.params`. -/
theorem instantiation_export_invokeOk {host : HostSemantics H} {before after : Store H}
    {m : V1.Module} {imports : List ExternVal} {module : ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hnh : NoHost10 before)
    (hs : StoreOk10 before) {x : Execution.Runtime.ExportInst} (hx : x ∈ module.exports)
    {a : FuncAddr} (hxa : x.value = .func a) :
    ∃ ft : V1.FuncType, FuncAt after ft a ∧ ∀ args : List Value, args.map Value.type = ft.params →
      Execution.Core.InvokeOk (coreStore10 after) a.value (args.map Value.toCore) := by
  obtain ⟨hF, hE⟩ := instantiation_funcs hI hnh hs
  obtain ⟨e, he, hev⟩ := hE x hx
  rw [hxa] at hev
  obtain ⟨et, het⟩ := hI.valid.exports e he
  cases hix : e.index with
  | func i =>
    rw [hix] at hev het
    simp only [exportValue?, Option.map_eq_some_iff, ExternVal.func.injEq] at hev
    simp only [exportType?, Option.map_eq_some_iff] at het
    obtain ⟨a', ha', rfl⟩ := hev
    obtain ⟨ft, hft, -⟩ := het
    obtain ⟨fi, hfi, hty⟩ := forall₂_getElem? hF hft ha'
    exact ⟨ft, ⟨fi, hfi, hty⟩, fun args hargs => invokeOk_of_v1 hfi (hty ▸ hargs)⟩
  | table i => rw [hix] at hev; simp [exportValue?] at hev
  | memory i => rw [hix] at hev; simp [exportValue?] at hev
  | global i => rw [hix] at hev; simp [exportValue?] at hev

/-! ## The forward run with no `InvokeOk` hypothesis -/

/-- **`Task.wholeRunFwd10Inv` for an exported function, with no Core hypothesis**: for the last
of a sequence of V1 instantiations from the empty store (`Reach10`, globals allowed, 32-bit
segment bounds), every exported function of the new instance has a validated type `ft`, and for
every argument list of V1 types `ft.params` whose invocation image is IL-typed, every V1 run of
the invocation is a run of the 1.0 script. -/
theorem wholeRunFwd10InvRUE {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : Silmaril.Wasm.Numerics.RelaxedChoice} {before s : Store H} {m : V1.Module}
    {imports : List ExternVal} {module : ModuleInst} {outcome : Execution.Runtime.Result}
    (hR : InstG.Reach10 before) (hI : Instantiation host before m imports s module outcome)
    (hb : InstG.InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    {x : Execution.Runtime.ExportInst} (hx : x ∈ module.exports) {a : FuncAddr}
    (hxa : x.value = .func a) :
    ∃ ft : V1.FuncType, FuncAt s ft a ∧ ∀ args : List Value, args.map Value.type = ft.params →
      ∀ c' : Config H, Typed10 (simEnv10 (Whole.fwdB10 nd r)) hn (invokeCfg10 s args a) →
        Steps host' (invokeCfg10 s args a) c' →
        Typed10 (simEnv10 (Whole.fwdB10 nd r)) hn c' ∧
          Relation.ReflTransGen (Sim.Round6.Reading.SStepB (simEnv10 (Whole.fwdB10 nd r)))
            (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  have ok := InstG.reach10_okU hR
  obtain ⟨ft, hfa, hft⟩ := instantiation_export_invokeOk hI ok.noHost ok.storeOk10 hx hxa
  exact ⟨ft, hfa, fun args hargs c' hc h =>
    InstG.wholeRunFwd10InvRU (.inst hR hI hb) hc (hft args hargs) h⟩

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvRTUE {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : Silmaril.Wasm.Numerics.RelaxedChoice} {before s : Store H} {m : V1.Module}
    {imports : List ExternVal} {module : ModuleInst} {outcome : Execution.Runtime.Result}
    (hR : InstG.Reach10 before) (hI : Instantiation host before m imports s module outcome)
    (hb : InstG.InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    {x : Execution.Runtime.ExportInst} (hx : x ∈ module.exports) {a : FuncAddr}
    (hxa : x.value = .func a) :
    ∃ ft : V1.FuncType, FuncAt s ft a ∧ ∀ args : List Value, args.map Value.type = ft.params →
      ∀ c' : Config H,
        Typed10 (StoreFix.simEnv10T (Whole.fwdB10 nd r)) hn (invokeCfg10 s args a) →
        Steps host' (invokeCfg10 s args a) c' →
        Typed10 (StoreFix.simEnv10T (Whole.fwdB10 nd r)) hn c' ∧
          Relation.ReflTransGen
            (Sim.Round6.Reading.SStepB (StoreFix.simEnv10T (Whole.fwdB10 nd r)))
            (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  have ok := InstG.reach10_okU hR
  obtain ⟨ft, hfa, hft⟩ := instantiation_export_invokeOk hI ok.noHost ok.storeOk10 hx hxa
  exact ⟨ft, hfa, fun args hargs c' hc h =>
    InstG.wholeRunFwd10InvRTU (.inst hR hI hb) hc (hft args hargs) h⟩

end Silmaril.Wasm.SpecTec.Sim10.InstInvoke
