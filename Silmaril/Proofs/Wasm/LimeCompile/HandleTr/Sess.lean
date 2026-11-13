module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Lists
public import Silmaril.Wasm.LimeCompile.Preserve.Defs

/-!
# The handle compiler on forwarders: one invocation

Source `M` (functions only, forwarding bodies, 2.0 function types `ts`) and target
`tgtM M` (`M` with every type rewritten by `hRec`) allocated from the same store `s`: the stores
`srcStore`/`tgtStore` append the same function bodies, typed `toDefType t` and
`toDefType (hV2FT t)`; the instances share their exports.

* `export_info`: an exported function address is a new function, with the source and target
  instances above and the API parameter types of `t`;
* `call_tgt`: a target invocation of an export with related arguments is well typed only if the
  source one is; the target does not diverge; its result is matched by a source run, with
  results related by `Handle.ResRel σ`;
* `call_src`: the converse.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (exportFunc?)
open Silmaril.Wasm.LimeCompile.HandleTr
open Silmaril.Wasm.LimeCompile.Handle (handleRef ResRel paramsOf)
open Silmaril.Wasm.LimeCompile.Preserve.Module (exportApi resolve typeAt)
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy)

variable {H : Type}

/-- The target module on the forwarder fragment: the types rewritten. -/
def tgtM (M : Module) : Module := { M with types := M.types.map hRec }

/-- The allocated source store. -/
def srcStore (s : Store H) (M : Module) (fts : List DefType) (xi : List ExportInst) : Store H :=
  { s with funcs := s.funcs ++ (fts.zip M.funcs).map fun p => ⟨p.1, onlyInst s M xi, .wasm p.2⟩ }

/-- The allocated target store. -/
def tgtStore (s : Store H) (M : Module) (fts' : List DefType) (xi : List ExportInst) :
    Store H :=
  { s with funcs := s.funcs ++
      (fts'.zip M.funcs).map fun p => ⟨p.1, onlyInst s (tgtM M) xi, .wasm p.2⟩ }

/-- The setting of one forwarder allocation. -/
structure Setup (s : Store H) (M : Module) (ts : List V2.FuncType) (fts fts' : List DefType)
    (xi : List ExportInst) : Prop where
  only : onlyFuncs M = true
  fwd : ∀ f ∈ M.funcs, fwdFunc f = true
  types : M.types = ts.map V2.FuncType.toCoreRec
  xi : M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi
  fts : M.funcs.mapM (fun fn => (ts.map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts
  fts' : M.funcs.mapM (fun fn => ((ts.map hV2FT).map V2.FuncType.toDefType)[fn.type.toNat]?) =
    some fts'

theorem exportFunc_tgt (s : Store H) (M : Module) (xi : List ExportInst) (x : String) :
    exportFunc? (onlyInst s (tgtM M) xi) x = exportFunc? (onlyInst s M xi) x := rfl

theorem typeDefinitions_v2 (ts : List V2.FuncType) :
    (Module.typeDefinitions { types := ts.map V2.FuncType.toCoreRec } : List SubType) =
      ts.map fun t => ⟨true, [], .func t.toCore⟩ := by
  simp only [Module.typeDefinitions, V2.FuncType.toCoreRec, List.flatMap_map]
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih]

theorem allocExport_name {mi : ModuleInst} {e : Export} {e' : ExportInst}
    (h : allocExport? mi e = some e') : e'.name = e.name := by
  unfold allocExport? at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

theorem allocExport_func {s : Store H} {M : Module} {e : Export} {x : String} {a : Nat}
    (h : allocExport? (onlyExpInst s M) e = some ⟨x, .func a⟩) :
    ∃ y : FuncIdx, e.index = .func y ∧ y.toNat < M.funcs.length ∧ a = s.funcs.length + y.toNat := by
  unfold allocExport? at h
  obtain ⟨b, hb, hbe⟩ := Option.map_eq_some_iff.mp h
  simp only [ExportInst.mk.injEq] at hbe
  obtain ⟨-, rfl⟩ := hbe
  cases hi : e.index with
  | func y =>
    rw [hi] at hb
    simp only [onlyExpInst, List.getElem?_map] at hb
    obtain ⟨n, hn, hnb⟩ := Option.map_eq_some_iff.mp hb
    simp only [ExternAddr.func.injEq] at hnb
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨hlt, hm'⟩ := List.getElem?_eq_some_iff.mp hm
    simp only [List.getElem_range] at hm'
    subst hm'
    exact ⟨y, rfl, by simpa using hlt, hnb.symm⟩
  | tag y => rw [hi] at hb; simp [onlyExpInst] at hb
  | global y => rw [hi] at hb; simp [onlyExpInst] at hb
  | memory y => rw [hi] at hb; simp [onlyExpInst] at hb
  | table y => rw [hi] at hb; simp [onlyExpInst] at hb

/-- An exported function address is that of a new function. -/
theorem export_addr {s : Store H} {M : Module} {xi : List ExportInst}
    (hxi : M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi) {x : String} {a : Nat}
    (ha : exportFunc? (onlyInst s M xi) x = some a) :
    ∃ e y, M.exports.find? (fun e => e.name == x) = some e ∧ e.index = .func y ∧
      y.toNat < M.funcs.length ∧ a = s.funcs.length + y.toNat := by
  have hfind : xi.find? (fun e => e.name == x) =
      (M.exports.find? (fun e => e.name == x)).bind (allocExport? (onlyExpInst s M)) :=
    find?_mapM (fun e e' he => by rw [allocExport_name he]) hxi
  have ha' : (match xi.find? (fun e => e.name == x) with
      | some ⟨_, .func a⟩ => some a | _ => none) = some a := ha
  rw [hfind] at ha'
  cases he : M.exports.find? (fun e => e.name == x) with
  | none => simp [he] at ha'
  | some e =>
    show ∃ e' y, some e = some e' ∧ _
    cases hg : allocExport? (onlyExpInst s M) e with
    | none => simp [he, hg] at ha'
    | some e' =>
      show ∃ e' y, some e = some e' ∧ _
      obtain ⟨xn, xa⟩ := e'
      cases xa with
      | func a' =>
        have haa : a' = a := by simpa [he, hg] using ha'
        obtain ⟨y, hy, hlt, hay⟩ : ∃ y : FuncIdx, e.index = .func y ∧
            y.toNat < M.funcs.length ∧ a' = s.funcs.length + y.toNat := allocExport_func hg
        exact ⟨e, y, rfl, hy, hlt, haa ▸ hay⟩
      | _ => simp [he, hg] at ha'

/-- The store entries of a new function. -/
theorem new_func {s : Store H} {M : Module} {ts : List V2.FuncType} {fts fts' : List DefType}
    {xi : List ExportInst} (hS : Setup s M ts fts fts' xi) {i : Nat} (hi : i < M.funcs.length) :
    ∃ f t, M.funcs[i]? = some f ∧ ts[f.type.toNat]? = some t ∧
      (srcStore s M fts xi).funcs[s.funcs.length + i]? =
        some ⟨t.toDefType, onlyInst s M xi, .wasm f⟩ ∧
      (tgtStore s M fts' xi).funcs[s.funcs.length + i]? =
        some ⟨(hV2FT t).toDefType, onlyInst s (tgtM M) xi, .wasm f⟩ := by
  obtain ⟨f, hf⟩ : ∃ f, M.funcs[i]? = some f := ⟨_, List.getElem?_eq_getElem hi⟩
  have hlen : fts.length = M.funcs.length := length_mapM' hS.fts
  have hlen' : fts'.length = M.funcs.length := length_mapM' hS.fts'
  have hft : fts[i]? = (ts.map V2.FuncType.toDefType)[f.type.toNat]? := by
    rw [getElem?_mapM hS.fts i, hf, Option.bind_some]
  obtain ⟨d, hd⟩ : ∃ d, fts[i]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨t, ht, hdt⟩ : ∃ t, ts[f.type.toNat]? = some t ∧ t.toDefType = d :=
    Option.map_eq_some_iff.mp (by rw [← List.getElem?_map, ← hft, hd])
  have hft' : fts'[i]? = some (hV2FT t).toDefType := by
    rw [getElem?_mapM hS.fts' i, hf, Option.bind_some, List.getElem?_map, List.getElem?_map, ht]
    rfl
  refine ⟨f, t, hf, ht, ?_, ?_⟩
  · rw [srcStore, List.getElem?_append_right (by omega)]
    simp [List.getElem?_map, List.getElem?_zip_eq_some, hd, hf, hdt]
  · rw [tgtStore, List.getElem?_append_right (by omega)]
    simp [List.getElem?_map, List.getElem?_zip_eq_some, hft', hf]

/-- The API parameter types of an exported new function. -/
theorem export_params {M : Module} {ts : List V2.FuncType}
    (hts : M.types = ts.map V2.FuncType.toCoreRec) (hi : M.imports = []) {x : String} {e : Export}
    {y : FuncIdx} {f : Func} {t : V2.FuncType} (he : M.exports.find? (fun e => e.name == x) = some e)
    (hy : e.index = .func y) (hf : M.funcs[y.toNat]? = some f) (ht : ts[f.type.toNat]? = some t) :
    paramsOf (exportApi M) x = some (t.params.map V2.ValType.toCore) := by
  have hfind : (exportApi M).find? (fun p => p.1 == x) = some (e.name, resolve M e.index) := by
    rw [show exportApi M = M.exports.map (fun e => (e.name, resolve M e.index)) from rfl,
      List.find?_map]
    exact congrArg (Option.map _) he
  have hfty : M.functionTypes[y.value.val]? = some f.type := by
    simp only [Module.functionTypes, Module.importedFunctions, hi, List.filterMap_nil,
      List.nil_append, List.getElem?_map]
    simpa [Idx.toNat] using congrArg (Option.map Func.type) hf
  have hdefs : M.typeDefinitions = ts.map fun t => (⟨true, [], .func t.toCore⟩ : SubType) := by
    rw [← typeDefinitions_v2 ts]
    simp [Module.typeDefinitions, hts]
  have hta : typeAt M f.type = some ⟨true, [], .func t.toCore⟩ := by
    unfold typeAt
    rw [hdefs, List.getElem?_map]
    simpa [Idx.toNat] using congrArg (Option.map _) ht
  have hres : resolve M e.index = some (.func ⟨true, [], .func t.toCore⟩) := by
    rw [hy]
    simp only [resolve, hfty, Option.bind_some, hta, Option.map_some]
  unfold paramsOf
  rw [hfind, hres]
  simp [V2.FuncType.toCore, V2.ResultType.toCore]

/-- **What an exported function address is.** -/
theorem export_info {s : Store H} {M : Module} {ts : List V2.FuncType} {fts fts' : List DefType}
    {xi : List ExportInst} (hS : Setup s M ts fts fts' xi) {x : String} {a : Nat}
    (ha : exportFunc? (onlyInst s M xi) x = some a) :
    ∃ f t, f ∈ M.funcs ∧
      (srcStore s M fts xi).funcs[a]? = some ⟨t.toDefType, onlyInst s M xi, .wasm f⟩ ∧
      (tgtStore s M fts' xi).funcs[a]? =
        some ⟨(hV2FT t).toDefType, onlyInst s (tgtM M) xi, .wasm f⟩ ∧
      paramsOf (exportApi M) x = some (t.params.map V2.ValType.toCore) := by
  obtain ⟨e, y, he, hy, hlt, rfl⟩ := export_addr hS.xi ha
  obtain ⟨f, t, hf, ht, hsrc, htgt⟩ := new_func hS hlt
  exact ⟨f, t, List.mem_of_getElem? hf, hsrc, htgt,
    export_params hS.types (onlyFuncs_fields hS.only).1 he hy hf ht⟩

theorem paramsOf_args {σ : List Val} {A : List (String × Option ApiTy)} {x : String}
    {ps : List ValType} {ws vs : List Val} (hp : paramsOf A x = some ps)
    (h : CallRelT σ A (x, ws) (x, vs)) : ArgsRelT σ ps ws vs := by
  have h2 := h.2
  simp only [hp] at h2
  exact h2

theorem toC_hV2 (t : V2.FuncType) :
    (hV2FT t).params.map V2.ValType.toC = t.params.map fun τ => (hV2val τ).toC := by
  simp [hV2FT, List.map_map, Function.comp_def]

theorem toC_hV2_results (t : V2.FuncType) :
    (Ty.ofList ((hV2FT t).results.map V2.ValType.toC)).length =
      (Ty.ofList (t.results.map V2.ValType.toC)).length := by
  simp [Ty.length, hV2FT]

/-- The arguments of a well-typed invocation of a function of 2.0 type `t`. -/
theorem invokeOk_args {S : Store H} {a : Nat} {fi : FuncInst H} {t : V2.FuncType} {vs : List Val}
    (hf : S.funcs[a]? = some fi) (hty : fi.type = t.toDefType) (hok : InvokeOk S a vs) :
    List.Forall₂ (ValOk S) vs (t.params.map V2.ValType.toC) := by
  obtain ⟨fi', ps, rs, hf', he, hv⟩ := hok
  have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have he2 : (Ty.func ps rs : CCompType) = .func (Ty.ofList (t.params.map V2.ValType.toC))
      (Ty.ofList (t.results.map V2.ValType.toC)) :=
    Silmaril.Wasm.SingleThreaded.Det.Expand.det (hty ▸ hfi ▸ he) (V2.Validation.expand_toDefType t)
  have hps : ps = Ty.ofList (t.params.map V2.ValType.toC) := by simpa using (by simpa using he2 :
    ps = _ ∧ rs = _).1
  simpa [hps] using hv

theorem invokeOk_of_args {S : Store H} {a : Nat} {fi : FuncInst H} {t : V2.FuncType}
    {vs : List Val} (hf : S.funcs[a]? = some fi) (hty : fi.type = t.toDefType)
    (hv : List.Forall₂ (ValOk S) vs (t.params.map V2.ValType.toC)) : InvokeOk S a vs :=
  ⟨fi, _, _, hf, hty ▸ V2.Validation.expand_toDefType t, by simpa using hv⟩

theorem argsRelT_length {σ : List Val} {τs : List V2.ValType} {ws vs : List Val}
    (h : ArgsRelT σ (τs.map V2.ValType.toCore) ws vs) (hw : ws.length = τs.length) :
    vs.length = τs.length := by
  unfold ArgsRelT at h
  by_cases hl : vs.length = (τs.map V2.ValType.toCore).length
  · simpa using hl
  · have hl' : ¬ vs.length = τs.length := by simpa using hl
    have hwv : ws = vs := by simpa [hl'] using h
    rw [← hwv, hw]

theorem argsRelT_at {σ : List Val} {τs : List V2.ValType} {ws vs : List Val}
    (h : ArgsRelT σ (τs.map V2.ValType.toCore) ws vs) (hl : vs.length = τs.length) :
    ArgsAt σ τs ws vs := by
  unfold ArgsRelT at h
  simp only [List.length_map, hl, ↓reduceIte] at h
  exact h

/-- The forwarding data of a new function. -/
theorem fwdAt_of {S : Store H} {a : Nat} {mi : ModuleInst} {f : Func} {t : V2.FuncType}
    {vs : List Val} (hf : S.funcs[a]? = some ⟨t.toDefType, mi, .wasm f⟩) (hfwd : fwdFunc f = true)
    (hl : vs.length = t.params.length) (hnf : NoFuncRef vs) :
    ∃ js, FwdAt S a ⟨t.toDefType, mi, .wasm f⟩ f (Ty.ofList (t.params.map V2.ValType.toC))
      (Ty.ofList (t.results.map V2.ValType.toC)) js vs := by
  obtain ⟨hloc, js, hbody⟩ := fwd_body hfwd
  exact ⟨js, hf, rfl, V2.Validation.expand_toDefType t, hloc, hbody, by simp [Ty.length, hl], hnf⟩

theorem fwd_body_eq {S S' : Store H} {a : Nat} {fi fi' : FuncInst H} {fn : Func}
    {ps rs ps' rs' : Ty (.list .val)} {js js' : List LocalIdx} {vs ws : List Val}
    (h : FwdAt S a fi fn ps rs js vs) (h' : FwdAt S' a fi' fn ps' rs' js' ws) : js = js' := by
  have hb : js.map Instr.localGet = js'.map Instr.localGet := h.hbody.symm.trans h'.hbody
  exact List.map_injective_iff.mpr (fun _ _ hj => by cases hj; rfl) hb

section
variable {s : Store H} {M : Module} {ts : List V2.FuncType} {fts fts' : List DefType}
  {xi : List ExportInst} {P : Profile} {host : HostSemantics H} {σ : List Val} {x : String}
  {a : Nat} {ws vs : List Val}

/-- **A target invocation is matched by the source.** -/
theorem call_tgt (hS : Setup s M ts fts fts' xi)
    (ha : exportFunc? (onlyInst s M xi) x = some a)
    (hrel : CallRelT σ (exportApi M) (x, ws) (x, vs))
    (hok' : InvokeOk (tgtStore s M fts' xi) a ws) :
    InvokeOk (srcStore s M fts xi) a vs ∧ ¬ Diverges P host (invoke (tgtStore s M fts' xi) a ws) ∧
      ∀ d (r : Result), Steps P host (invoke (tgtStore s M fts' xi) a ws) d → d.code = r.toAdmin →
        d.store = tgtStore s M fts' xi ∧ ∃ us' us, r = .values us' ∧
          Steps P host (invoke (srcStore s M fts xi) a vs) ⟨srcStore s M fts xi, {}, vals us⟩ ∧
          List.Forall₂ (ResRel σ) us' us := by
  obtain ⟨f, t, hfm, hsf, htf, hpar⟩ := export_info hS ha
  have hargs : ArgsRelT σ (t.params.map V2.ValType.toCore) ws vs := paramsOf_args hpar hrel
  have hvok' : List.Forall₂ (ValOk (tgtStore s M fts' xi)) ws
      (t.params.map fun τ => (hV2val τ).toC) := by
    simpa [toC_hV2] using invokeOk_args htf rfl hok'
  have hl' : vs.length = t.params.length :=
    argsRelT_length hargs (by simpa using List.Forall₂.length_eq hvok')
  have hat : ArgsAt σ t.params ws vs := argsRelT_at hargs hl'
  obtain ⟨hvok, hnfv⟩ : List.Forall₂ (ValOk (srcStore s M fts xi)) vs
      (t.params.map V2.ValType.toC) ∧ NoFuncRef vs := args_src hat hl' hvok'
  have hnfw : NoFuncRef ws := (args_tgt (s' := tgtStore s M fts' xi) hat hvok).2.1
  obtain ⟨js, hFs⟩ := fwdAt_of hsf (hS.fwd f hfm) hl' hnfv
  obtain ⟨js', hFt⟩ := fwdAt_of htf (hS.fwd f hfm)
    (by simpa [hV2FT] using (List.Forall₂.length_eq hvok')) hnfw
  have hjs : js = js' := fwd_body_eq hFs hFt
  refine ⟨invokeOk_of_args hsf rfl hvok, invoke_not_diverges hFt, ?_⟩
  intro d r hd hr
  obtain ⟨us', hus', hlen', hdeq, hreq⟩ : ∃ us', proj js' ws = some us' ∧
      us'.length = (Ty.ofList ((hV2FT t).results.map V2.ValType.toC)).length ∧
      d = ⟨tgtStore s M fts' xi, {}, vals us'⟩ ∧ r = .values us' := invoke_result hFt hd hr
  obtain ⟨hl2, hget⟩ := args_get hat hl'
  obtain ⟨us, hus, hrelu⟩ : ∃ us, proj js vs = some us ∧ List.Forall₂ (ResRel σ) us' us :=
    proj_rel hl2 hget (hjs ▸ hus')
  have hlen : us.length = (Ty.ofList (t.results.map V2.ValType.toC)).length := by
    rw [proj_length hus, hjs, ← proj_length hus', hlen', toC_hV2_results]
  exact ⟨by rw [hdeq], us', us, hreq, invoke_run hFs hus hlen, hrelu⟩

/-- **A source invocation is matched by the target.** -/
theorem call_src (hS : Setup s M ts fts fts' xi)
    (ha : exportFunc? (onlyInst s M xi) x = some a)
    (hrel : CallRelT σ (exportApi M) (x, ws) (x, vs))
    (hok : InvokeOk (srcStore s M fts xi) a vs) :
    InvokeOk (tgtStore s M fts' xi) a ws ∧ ¬ Diverges P host (invoke (srcStore s M fts xi) a vs) ∧
      ∀ d (r : Result), Steps P host (invoke (srcStore s M fts xi) a vs) d → d.code = r.toAdmin →
        d.store = srcStore s M fts xi ∧ ∃ us us', r = .values us ∧
          Steps P host (invoke (tgtStore s M fts' xi) a ws) ⟨tgtStore s M fts' xi, {}, vals us'⟩ ∧
          List.Forall₂ (ResRel σ) us' us := by
  obtain ⟨f, t, hfm, hsf, htf, hpar⟩ := export_info hS ha
  have hargs : ArgsRelT σ (t.params.map V2.ValType.toCore) ws vs := paramsOf_args hpar hrel
  have hvok : List.Forall₂ (ValOk (srcStore s M fts xi)) vs (t.params.map V2.ValType.toC) :=
    invokeOk_args hsf rfl hok
  have hl' : vs.length = t.params.length := by simpa using List.Forall₂.length_eq hvok
  have hat : ArgsAt σ t.params ws vs := argsRelT_at hargs hl'
  obtain ⟨hwok, hnfw, hnfv⟩ : List.Forall₂ (ValOk (tgtStore s M fts' xi)) ws
      (t.params.map fun τ => (hV2val τ).toC) ∧ NoFuncRef ws ∧ NoFuncRef vs := args_tgt hat hvok
  obtain ⟨js, hFs⟩ := fwdAt_of hsf (hS.fwd f hfm) hl' hnfv
  obtain ⟨js', hFt⟩ := fwdAt_of htf (hS.fwd f hfm)
    (by simpa [hV2FT] using (List.Forall₂.length_eq hwok)) hnfw
  have hjs : js = js' := fwd_body_eq hFs hFt
  refine ⟨invokeOk_of_args htf rfl (by simpa [toC_hV2] using hwok), invoke_not_diverges hFs, ?_⟩
  intro d r hd hr
  obtain ⟨us, hus, hlen, hdeq, hreq⟩ : ∃ us, proj js vs = some us ∧
      us.length = (Ty.ofList (t.results.map V2.ValType.toC)).length ∧
      d = ⟨srcStore s M fts xi, {}, vals us⟩ ∧ r = .values us := invoke_result hFs hd hr
  obtain ⟨hl2, hget⟩ := args_get hat hl'
  obtain ⟨us', hus', hrelu⟩ : ∃ us', proj js ws = some us' ∧ List.Forall₂ (ResRel σ) us' us :=
    proj_rel' hl2 hget hus
  have hlen' : us'.length = (Ty.ofList ((hV2FT t).results.map V2.ValType.toC)).length := by
    rw [proj_length hus', ← proj_length hus, hlen, toC_hV2_results]
  exact ⟨by rw [hdeq], us, us', hreq, invoke_run hFt (hjs ▸ hus') hlen', hrelu⟩

end

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
