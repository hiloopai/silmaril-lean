module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostImpl10

/-!
# Runs that call host functions: Core hypotheses and the forward run

* `ImplOk ι σ`: the Core image of every implementation, in its closed module instance, is a
  valid Core function instance (at every Core store; the module instance refers to none of it).
* **`storeOk_impl`**: under `HostTyped σ` and `ImplOk ι σ`, the Core image of `implS ι s` is
  valid when that of `s` is. Defined functions keep their validity (`storeOk_withFuncs`).
* `invokeOk_impl`, `storeWF_impl`: Core's `InvokeOk` and the simulation's `StoreWF` move to the
  implemented store.
* **`wholeRunFwd10Impl`**, `wholeRunFwd10ImplT`: round 4's `Task.wholeRunFwd10Inv` for V1 runs
  under **any host with an implementation**, host calls included: the run between the
  implemented configurations is a run of the 1.0 script.
* **`wholeRunFwd10ImplRH`**, `wholeRunFwd10ImplRHT`: the same at every store reached by
  instantiations from a base store, with Core's `InvokeOk` derived from
  V1 data (a function at the address, arguments of its parameter types; `invokeOk_of_v1`)
  rather than assumed.
* `wholeRunFwd10InvRHV`, `wholeRunFwd10InvRHVT`: round 6's `wholeRunFwd10InvRH` with the same
  V1 data in place of Core's `InvokeOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostRead

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps values)
open Silmaril.Wasm.Execution.Runtime (Value FuncInst FuncAddr ModuleInst)
open Silmaril.Wasm.Execution.Core (StoreOk FuncInstOk)
open Silmaril.Wasm.Binaryen.InlS (withFuncs SameTypes storeOk_withFuncs funcInstOk_withFuncs
  valOk_withFuncs)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.InstH (ReachH10 reachH10_ok)
open Silmaril.Wasm.SpecTec.Sim10.InstInvoke (invokeOk_of_v1)
open Silmaril.Wasm.SpecTec.Sim10.HostStub (toC coreFuncs10 stubMod)

variable {H : Type}

/-! ## The implemented store is valid -/

/-- **Every implementation is a valid Core function instance** of its host code's signature,
in its closed module instance. -/
def ImplOk (ι : H → V1.Func) (σ : H → V1.FuncType) : Prop :=
  ∀ (h : H) (S : Execution.Core.Store H),
    FuncInstOk S (toC (.wasm (σ h) (stubMod (σ h)) (ι h) : FuncInst V1.Func H))

theorem coreStore10_impl (ι : H → V1.Func) (s : Store H) :
    coreStore10 (implS ι s) = withFuncs (coreStore10 s) ((s.funcs.map (implF ι)).map toC) := by
  have e : (coreStore10 (implS ι s)).funcs = (s.funcs.map (implF ι)).map toC :=
    coreFuncs10 (implS ι s)
  rw [← e]
  rfl

theorem sameTypes_impl (ι : H → V1.Func) (s : Store H) :
    SameTypes ((s.funcs.map (implF ι)).map toC) (coreStore10 s).funcs := by
  rw [coreFuncs10]
  simp only [SameTypes, List.map_map]
  apply List.map_congr_left
  intro fi _
  cases fi <;> rfl

/-- **The Core image of the implemented store is valid** when that of the store is, the host
functions have their signatures, and the implementations are valid. -/
theorem storeOk_impl {ι : H → V1.Func} {σ : H → V1.FuncType} {s : Store H}
    (hS : StoreOk (coreStore10 s)) (ht : HostTyped σ s.funcs) (hι : ImplOk ι σ) :
    StoreOk (coreStore10 (implS ι s)) := by
  rw [coreStore10_impl]
  refine storeOk_withFuncs hS (sameTypes_impl ι s) ?_
  intro fi' hfi'
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hfi'
  obtain ⟨fi, hfi, rfl⟩ := hfi'
  cases fi with
  | wasm t m fn =>
    have hok : FuncInstOk (coreStore10 s) (toC (.wasm t m fn)) :=
      hS.funcs _ (by rw [coreFuncs10]; exact List.mem_map_of_mem hfi)
    exact funcInstOk_withFuncs (sameTypes_impl ι s) hok
  | host t h =>
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
    have e : t = σ h := ht a t h ha
    subst e
    exact hι h _

/-- **Core's `InvokeOk` moves to the implemented store.** -/
theorem invokeOk_impl (ι : H → V1.Func) {s : Store H} {a : Nat} {vs : List Execution.Core.Val}
    (h : Execution.Core.InvokeOk (coreStore10 s) a vs) :
    Execution.Core.InvokeOk (coreStore10 (implS ι s)) a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hv⟩ := h
  obtain ⟨fi', hfi', hty⟩ := (sameTypes_impl ι s).get hfi
  rw [coreStore10_impl]
  exact ⟨fi', ps, rs, hfi', hty ▸ he, hv.imp fun _ _ h => valOk_withFuncs (sameTypes_impl ι s) h⟩

/-- **The simulation's `StoreWF` moves to the implemented store.** -/
theorem storeWF_impl (ι : H → V1.Func) {s : Store H}
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime)) :
    Lime1.Execution.StoreWF ((implS ι s).mapCode V1.Func.toLime) := by
  refine ⟨fun i t m c h => ?_, fun i mi h => hwf.2 i mi h⟩
  have hl : ((implS ι s).mapCode V1.Func.toLime).funcs.length =
      (s.mapCode V1.Func.toLime).funcs.length := by
    simp [implS, Execution.Runtime.Store.mapCode]
  intro a ha
  rw [hl]
  simp only [implS, Execution.Runtime.Store.mapCode, List.getElem?_map, List.map_map,
    Option.map_eq_some_iff, Function.comp_apply] at h
  obtain ⟨fi, hfi, he⟩ := h
  cases fi with
  | wasm t' m' fn' =>
    simp only [implF, Execution.Runtime.FuncInst.mapCode, FuncInst.wasm.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hwf.1 i t' m' (V1.Func.toLime fn')
      (by simp [Execution.Runtime.Store.mapCode, hfi, Execution.Runtime.FuncInst.mapCode]) a ha
  | host t' h' =>
    simp only [implF, Execution.Runtime.FuncInst.mapCode, FuncInst.wasm.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp [stubMod] at ha

/-! ## The forward run, host calls included -/

/-- **`Task.wholeRunFwd10Inv` for runs that call host functions**: under a host with an
implementation, every V1 run from an invocation, host calls included, is, read through the
implementation, a run of the 1.0 script. The typing hypothesis is on the implemented
invocation. -/
theorem wholeRunFwd10Impl {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s : Store H} {args : List Value}
    {a : FuncAddr} {c' : Config H} (hH : HostImpl ι σ host) (hι : ImplOk ι σ)
    (ht : HostTyped σ s.funcs)
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 (implS ι s) args a))
    (hs : StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (implC ι c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (implC ι (invokeCfg10 s args a))) (configV hn (implC ι c')) :=
  wholeRunFwd10Inv H hn emptyHost10 nd r (implS ι s) args a (implC ι c') hc
    (storeOk_impl hs ht hι) (invokeOk_impl ι hinv) (storeWF_impl ι hwf)
    (steps_impl hH h ht).2

/-- **The same in `simEnv10T`** (the `STORE`-corrected script). -/
theorem wholeRunFwd10ImplT {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s : Store H} {args : List Value}
    {a : FuncAddr} {c' : Config H} (hH : HostImpl ι σ host) (hι : ImplOk ι σ)
    (ht : HostTyped σ s.funcs)
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 (implS ι s) args a))
    (hs : StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (implC ι c') ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (implC ι (invokeCfg10 s args a))) (configV hn (implC ι c')) :=
  wholeRunFwd10InvT (host := emptyHost10) hc (storeOk_impl hs ht hι) (invokeOk_impl ι hinv)
    (storeWF_impl ι hwf) (steps_impl hH h ht).2

/-- **At every store reached from a base store**, with Core's `InvokeOk`
derived from a V1 function instance at the address and arguments of its parameter types. -/
theorem wholeRunFwd10ImplRH {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s₀ s : Store H} (hR : ReachH10 s₀ s)
    (h₀ : StoreOk (coreStore10 s₀)) (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : FuncAddr} {fi : FuncInst V1.Func H} {c' : Config H}
    (hH : HostImpl ι σ host) (hι : ImplOk ι σ) (ht : HostTyped σ s.funcs)
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 (implS ι s) args a))
    (hf : s.funcs[a.value]? = some fi) (hty : args.map Value.type = fi.type.params)
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (implC ι c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (implC ι (invokeCfg10 s args a))) (configV hn (implC ι c')) :=
  wholeRunFwd10Impl hH hι ht hc (reachH10_ok hR h₀ hw₀).1 (invokeOk_of_v1 hf hty)
    (reachH10_ok hR h₀ hw₀).2 h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10ImplRHT {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s₀ s : Store H} (hR : ReachH10 s₀ s)
    (h₀ : StoreOk (coreStore10 s₀)) (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : FuncAddr} {fi : FuncInst V1.Func H} {c' : Config H}
    (hH : HostImpl ι σ host) (hι : ImplOk ι σ) (ht : HostTyped σ s.funcs)
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 (implS ι s) args a))
    (hf : s.funcs[a.value]? = some fi) (hty : args.map Value.type = fi.type.params)
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (implC ι c') ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (implC ι (invokeCfg10 s args a))) (configV hn (implC ι c')) :=
  wholeRunFwd10ImplT hH hι ht hc (reachH10_ok hR h₀ hw₀).1 (invokeOk_of_v1 hf hty)
    (reachH10_ok hR h₀ hw₀).2 h

/-! ## Round 6's `ReachH10` forms without Core's `InvokeOk` -/

/-- **Round 6's `wholeRunFwd10InvRH` with V1 data in place of Core's `InvokeOk`.** -/
theorem wholeRunFwd10InvRHV {hn : H → String} {host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s₀ s : Store H} (hR : ReachH10 s₀ s)
    (h₀ : StoreOk (coreStore10 s₀)) (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : FuncAddr} {fi : FuncInst V1.Func H} {c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hf : s.funcs[a.value]? = some fi) (hty : args.map Value.type = fi.type.params)
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  InstH.wholeRunFwd10InvRH hR h₀ hw₀ hc (invokeOk_of_v1 hf hty) h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvRHVT {hn : H → String} {host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s₀ s : Store H} (hR : ReachH10 s₀ s)
    (h₀ : StoreOk (coreStore10 s₀)) (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : FuncAddr} {fi : FuncInst V1.Func H} {c' : Config H}
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hf : s.funcs[a.value]? = some fi) (hty : args.map Value.type = fi.type.params)
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  InstH.wholeRunFwd10InvRHT hR h₀ hw₀ hc (invokeOk_of_v1 hf hty) h

end Silmaril.Wasm.SpecTec.Sim10.HostRead
