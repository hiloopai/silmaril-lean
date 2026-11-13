module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostImplCore10

/-!
# Runs that call host functions: Core's `InvokeOk` from V1 validation at host stores

Round 6's `instantiation_export_invokeOk` derives Core's `InvokeOk` for an exported function
from V1 module validation, but only after an instantiation from a store with **no** host
function: the start function's run must keep the function list, and a host call may change it.
Under a host with an implementation, the function list is kept up to the reading
(`hostImpl_funcs`), which keeps the function types. So:

* `prepare?_funcs_wasm`: preparation only appends defined functions.
* **`instantiation_funcsH`**: after a V1 instantiation under a host with an implementation, from
  a `HostTyped σ` store that may hold host functions, the instance's function addresses hold
  functions of the validation context's function types, and the result is `HostTyped σ`.
* **`instantiation_export_invokeOkH`**: so every exported function has a validated type `ft`,
  and Core's `InvokeOk` holds for every argument list of V1 types `ft.params`.
* **`wholeRunFwd10ImplRHE`**, `wholeRunFwd10ImplRHET`: the forward run, host calls included,
  for an exported function of the last of a sequence of instantiations from a base store with
  host functions, with **no Core hypothesis on the invocation**: Core validity of the base
  store, `StoreWF`, the 32-bit bounds and IL typing of the implemented invocation remain.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostRead

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps Instantiation allocate?
  prepare? applyData applyElem exportValue?)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal FuncInst FuncAddr ModuleInst)
open Silmaril.Wasm.V1.Validation (moduleContext exportType?)
open Silmaril.Wasm.Execution.Core (StoreOk)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.InstG (InstBoundsG)
open Silmaril.Wasm.SpecTec.Sim10.InstH (ReachH10 HostChain10 reachH10_ok)
open Silmaril.Wasm.SpecTec.Sim10.InstInvoke (FuncAt invokeOk_of_v1 prepare?_funcs forall₂_imp
  forall₂_getElem? foldl_applyElem_funcs steps_funcs10)

variable {H : Type}

/-! ## Preparation appends defined functions -/

/-- No entry of the list is a host function. -/
def AllWasm (fs : List (FuncInst V1.Func H)) : Prop :=
  ∀ (a : Nat) (t : V1.FuncType) (h : H), fs[a]? ≠ some (.host t h)

/-- **Allocation appends defined functions.** -/
theorem allocate?_funcs_wasm {s s₁ : Store H} {m : V1.Module} {imports : List ExternVal}
    {mi : ModuleInst} (h : allocate? s m imports = some (s₁, mi)) :
    ∃ fs : List (FuncInst V1.Func H), s₁.funcs = s.funcs ++ fs ∧ AllWasm fs := by
  unfold allocate? at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨inits, -, exps, -, fs, hfs, rfl, rfl⟩ := h
  refine ⟨fs, rfl, ?_⟩
  intro a t h' e
  obtain ⟨f, -, hfe⟩ := mapM_some_mem hfs _ (List.mem_of_getElem? e)
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hfe
  obtain ⟨ft, -, hfe⟩ := hfe
  cases hfe

/-- **Preparation appends defined functions.** -/
theorem prepare?_funcs_wasm {s : Store H} {m : V1.Module} {imports : List ExternVal}
    {p : V1.Execution.Prepared H} (h : prepare? s m imports = some p) :
    ∃ fs : List (FuncInst V1.Func H), p.store.funcs = s.funcs ++ fs ∧ AllWasm fs := by
  obtain ⟨s₁, mi, elems, data, ha, -, hp⟩ := prepare_store h
  obtain ⟨fs, hfs, hw⟩ := allocate?_funcs_wasm ha
  refine ⟨fs, ?_, hw⟩
  rw [hp, (foldl_applyData _ data).1, foldl_applyElem_funcs, hfs]

/-- `HostTyped` survives appending defined functions. -/
theorem hostTyped_append {σ : H → V1.FuncType} {l fs : List (FuncInst V1.Func H)}
    (ht : HostTyped σ l) (hw : AllWasm fs) : HostTyped σ (l ++ fs) := by
  intro a t h e
  rcases Nat.lt_or_ge a l.length with hl | hl
  · rw [List.getElem?_append_left hl] at e
    exact ht a t h e
  · rw [List.getElem?_append_right hl] at e
    exact absurd e (hw _ t h)

/-- `FuncAt` moves along an equality of the read function lists. -/
theorem funcAt_of_map {ι : H → V1.Func} {s s' : Store H}
    (he : s'.funcs.map (implF ι) = s.funcs.map (implF ι)) {ft : V1.FuncType} {a : FuncAddr}
    (h : FuncAt s ft a) : FuncAt s' ft a := by
  obtain ⟨fi, hf, hty⟩ := h
  have e := congrArg (fun l => l[a.value]?) he
  simp only [List.getElem?_map, hf, Option.map_some] at e
  obtain ⟨fi', hf', hfe⟩ := Option.map_eq_some_iff.mp e
  refine ⟨fi', hf', ?_⟩
  rw [← hty, ← implF_type ι fi', hfe, implF_type]

/-! ## After an instantiation under a host with an implementation -/

/-- **After a V1 instantiation under a host with an implementation, from a `HostTyped σ`
store**, the instance's function addresses hold functions of the validation context's types, its
exports come from the module's, and the result is `HostTyped σ`. -/
theorem instantiation_funcsH {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    {before after : Store H} {m : V1.Module} {imports : List ExternVal} {module : ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hH : HostImpl ι σ host)
    (ht : HostTyped σ before.funcs) :
    List.Forall₂ (FuncAt after) (moduleContext m).funcs module.funcs ∧
      (∀ x ∈ module.exports, ∃ e ∈ m.exports, exportValue? module e.index = some x.value) ∧
      HostTyped σ after.funcs := by
  obtain ⟨p, hp, rfl, hst⟩ := hI.prepared
  obtain ⟨fs, hfs, hw⟩ := prepare?_funcs_wasm hp
  have htp : HostTyped σ p.store.funcs := hfs ▸ hostTyped_append ht hw
  obtain ⟨hta, hrun⟩ := steps_impl hH hst htp
  have he : after.funcs.map (implF ι) = p.store.funcs.map (implF ι) :=
    steps_funcs10 hrun (noHost10_implS ι _)
  obtain ⟨hF, hE⟩ := prepare?_funcs hI.importsMatch hp
  exact ⟨forall₂_imp (fun ft a h => funcAt_of_map he h) hF, hE, hta⟩

/-- **Core's `InvokeOk` for an exported function, from V1 validation, at a store with host
functions**: under a host with an implementation, every exported function of the instance has a
validated type `ft`, and `InvokeOk` holds for every argument list of V1 types `ft.params`. -/
theorem instantiation_export_invokeOkH {ι : H → V1.Func} {σ : H → V1.FuncType}
    {host : HostSemantics H} {before after : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : ModuleInst} {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hH : HostImpl ι σ host)
    (ht : HostTyped σ before.funcs) {x : Execution.Runtime.ExportInst} (hx : x ∈ module.exports)
    {a : FuncAddr} (hxa : x.value = .func a) :
    HostTyped σ after.funcs ∧ ∃ ft : V1.FuncType, FuncAt after ft a ∧
      ∀ args : List Value, args.map Value.type = ft.params →
        Execution.Core.InvokeOk (coreStore10 after) a.value (args.map Value.toCore) := by
  obtain ⟨hF, hE, hta⟩ := instantiation_funcsH hI hH ht
  obtain ⟨e, he, hev⟩ := hE x hx
  rw [hxa] at hev
  obtain ⟨et, het⟩ := hI.valid.exports e he
  refine ⟨hta, ?_⟩
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

/-! ## The forward run for an exported function, host calls included -/

/-- **`Task.wholeRunFwd10Inv` for an exported function at a store with host functions, host
calls included, with no Core hypothesis on the invocation.** For the last of a sequence of
instantiations from a base store `s₀` (`ReachH10`), under hosts with the implementation `ι`,
every exported function has a validated type `ft`, and for every argument list of V1 types
`ft.params` whose implemented invocation is IL-typed, every V1 run of the invocation is, read
through `ι`, a run of the 1.0 script. -/
theorem wholeRunFwd10ImplRHE {ι : H → V1.Func} {σ : H → V1.FuncType}
    {hostI host : HostSemantics H} {hn : H → String} {nd : Bool} {r : RelaxedChoice}
    {s₀ before s : Store H} {m : V1.Module} {imports : List ExternVal} {module : ModuleInst}
    {outcome : Execution.Runtime.Result} (hR : ReachH10 s₀ before)
    (h₀ : StoreOk (coreStore10 s₀)) (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    (hch : HostChain10 hostI) (hI : Instantiation hostI before m imports s module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hHI : HostImpl ι σ hostI) (hH : HostImpl ι σ host) (hι : ImplOk ι σ)
    (ht : HostTyped σ before.funcs) {x : Execution.Runtime.ExportInst} (hx : x ∈ module.exports)
    {a : FuncAddr} (hxa : x.value = .func a) :
    ∃ ft : V1.FuncType, FuncAt s ft a ∧ ∀ args : List Value, args.map Value.type = ft.params →
      ∀ c' : Config H, Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 (implS ι s) args a) →
        Steps host (invokeCfg10 s args a) c' →
        Typed10 (simEnv10 (fwdB10 nd r)) hn (implC ι c') ∧
          Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
            (configV hn (implC ι (invokeCfg10 s args a))) (configV hn (implC ι c')) := by
  obtain ⟨hts, ft, hfa, hft⟩ := instantiation_export_invokeOkH hI hHI ht hx hxa
  have ok := reachH10_ok (.inst hR hch hI hb) h₀ hw₀
  exact ⟨ft, hfa, fun args hargs c' hc h =>
    wholeRunFwd10Impl hH hι hts hc ok.1 (hft args hargs) ok.2 h⟩

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10ImplRHET {ι : H → V1.Func} {σ : H → V1.FuncType}
    {hostI host : HostSemantics H} {hn : H → String} {nd : Bool} {r : RelaxedChoice}
    {s₀ before s : Store H} {m : V1.Module} {imports : List ExternVal} {module : ModuleInst}
    {outcome : Execution.Runtime.Result} (hR : ReachH10 s₀ before)
    (h₀ : StoreOk (coreStore10 s₀)) (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    (hch : HostChain10 hostI) (hI : Instantiation hostI before m imports s module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hHI : HostImpl ι σ hostI) (hH : HostImpl ι σ host) (hι : ImplOk ι σ)
    (ht : HostTyped σ before.funcs) {x : Execution.Runtime.ExportInst} (hx : x ∈ module.exports)
    {a : FuncAddr} (hxa : x.value = .func a) :
    ∃ ft : V1.FuncType, FuncAt s ft a ∧ ∀ args : List Value, args.map Value.type = ft.params →
      ∀ c' : Config H, Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 (implS ι s) args a) →
        Steps host (invokeCfg10 s args a) c' →
        Typed10 (simEnv10T (fwdB10 nd r)) hn (implC ι c') ∧
          Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
            (configV hn (implC ι (invokeCfg10 s args a))) (configV hn (implC ι c')) := by
  obtain ⟨hts, ft, hfa, hft⟩ := instantiation_export_invokeOkH hI hHI ht hx hxa
  have ok := reachH10_ok (.inst hR hch hI hb) h₀ hw₀
  exact ⟨ft, hfa, fun args hargs c' hc h =>
    wholeRunFwd10ImplT hH hι hts hc ok.1 (hft args hargs) ok.2 h⟩

end Silmaril.Wasm.SpecTec.Sim10.HostRead
