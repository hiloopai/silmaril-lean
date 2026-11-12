module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostStub10
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

/-!
# The stub restatement: Core hypotheses and the forward run

* `funcInstOk_stubC`: the Core image of a stub is a valid Core function instance whenever its
  type is a valid function type (the body `unreachable` has every type).
* **`storeOk_stub`**: if the Core image of `s` is valid, so is that of `stubS s`. The stubs
  replace exactly the host functions, with the same types, and Core's host-function rule gives
  the type's validity; the other instances keep their validity (`storeOk_withFuncs`).
* `invokeOk_stub`, `storeWF_stub`: Core's `InvokeOk` and the simulation's `StoreWF` move to the
  stubbed store.
* **`wholeRunFwd10Stub`**, `wholeRunFwd10StubT`, **`wholeRunFwd10StubRH`**,
  `wholeRunFwd10StubRHT`: the forward run at stores with host functions, for runs that call no
  host function, read through the stub.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostStub

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps values)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal FuncInst ModuleInst)
open Silmaril.Wasm.Execution.Core (StoreOk FuncInstOk ModuleInstOk)
open Silmaril.Wasm.Binaryen.InlS (withFuncs SameTypes storeOk_withFuncs funcInstOk_withFuncs
  valOk_withFuncs)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.InstH (ReachH10 reachH10_ok)

variable {H : Type}

/-! ## The stub is a valid Core function instance -/

/-- The Core image of a V1 function instance. -/
abbrev toC (fi : FuncInst V1.Func H) : Execution.Core.FuncInst H :=
  (fi.mapCode V1.Func.toLime).toCore

/-- The validation context of the stub's module instance. -/
def stubCtx (t : V1.FuncType) : Context :=
  { types := [t.toDefType], recs := [], tags := [], globals := [], mems := [], tables := [],
    funcs := [], datas := [], elems := [], refs := List.range 0 }

theorem moduleOk_stub (S : Execution.Core.Store H) (t : V1.FuncType)
    (hdt : TyOk {} t.toDefType) : ModuleInstOk S (stubMod t).toCore (stubCtx t) := by
  refine ModuleInstOk.mk (tags := []) (globals := []) (funcs := []) (mems := []) (tables := [])
    (elems := []) (k := 0) ?_ .nil .nil .nil .nil .nil ?_ .nil ?_ List.nodup_nil ?_
    (Nat.zero_le _)
  · intro d hd
    have hd' : d = t.toDefType := List.mem_singleton.1 hd
    rw [hd']
    exact hdt
  · intro a ha
    exact absurd ha List.not_mem_nil
  · intro xi hx
    exact absurd hx List.not_mem_nil
  · intro xi hx
    exact absurd hx List.not_mem_nil

/-- **The Core image of a stub is a valid function instance** when its type is valid. -/
theorem funcInstOk_stubC (S : Execution.Core.Store H) (t : V1.FuncType) (h : H)
    (hdt : TyOk {} t.toDefType) {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} (he : Expand t.toDefType (.func ps rs)) :
    FuncInstOk S (toC (stubF (.host t h : FuncInst V1.Func H))) := by
  have hr := (Expand.func_ok (Execution.Core.TyOk.of_empty (stubCtx t).toTypeCtx hdt) he).2
  have hb : ExprOk ((stubCtx t).funcBody ps.toList rs.toList []) [.unreachable] rs.toList :=
    .instr (.parametric (.unreachable ⟨fun _ hx => absurd hx List.not_mem_nil, hr,
      fun _ hx => absurd hx List.not_mem_nil⟩))
  exact .wasm hdt (moduleOk_stub S t hdt) rfl (.mk rfl he .nil hb)
    (Sub.refl (k := .def) _ trivial _)

/-! ## The stubbed store -/

theorem coreFuncs10 (s : Store H) : (coreStore10 s).funcs = s.funcs.map toC := by
  simp [coreStore10, Execution.Runtime.Store.toCore, Execution.Runtime.Store.mapCode]

theorem coreStore10_stub (s : Store H) :
    coreStore10 (stubS s) = withFuncs (coreStore10 s) ((s.funcs.map stubF).map toC) := by
  have e : (coreStore10 (stubS s)).funcs = (s.funcs.map stubF).map toC := coreFuncs10 (stubS s)
  rw [← e]
  rfl

theorem sameTypes_stub (s : Store H) :
    SameTypes ((s.funcs.map stubF).map toC) (coreStore10 s).funcs := by
  rw [coreFuncs10]
  simp only [SameTypes, List.map_map]
  apply List.map_congr_left
  intro fi _
  cases fi <;> rfl

/-- **The Core image of the stubbed store is valid when that of the store is.** -/
theorem storeOk_stub {s : Store H} (hS : StoreOk (coreStore10 s)) :
    StoreOk (coreStore10 (stubS s)) := by
  rw [coreStore10_stub]
  refine storeOk_withFuncs hS (sameTypes_stub s) ?_
  intro fi' hfi'
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hfi'
  obtain ⟨fi, hfi, rfl⟩ := hfi'
  have hok : FuncInstOk (coreStore10 s) (toC fi) :=
    hS.funcs _ (by rw [coreFuncs10]; exact List.mem_map_of_mem hfi)
  cases fi with
  | wasm t m fn => exact funcInstOk_withFuncs (sameTypes_stub s) hok
  | host t h =>
    cases hok with
    | wasm _ _ hcode => cases hcode
    | host hdt he _ => exact funcInstOk_stubC _ t h hdt he

/-- **Core's `InvokeOk` moves to the stubbed store.** -/
theorem invokeOk_stub {s : Store H} {a : Nat} {vs : List Execution.Core.Val}
    (h : Execution.Core.InvokeOk (coreStore10 s) a vs) :
    Execution.Core.InvokeOk (coreStore10 (stubS s)) a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hv⟩ := h
  obtain ⟨fi', hfi', hty⟩ := (sameTypes_stub s).get hfi
  rw [coreStore10_stub]
  exact ⟨fi', ps, rs, hfi', hty ▸ he, hv.imp fun _ _ h => valOk_withFuncs (sameTypes_stub s) h⟩

/-- **The simulation's `StoreWF` moves to the stubbed store.** -/
theorem storeWF_stub {s : Store H} (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime)) :
    Lime1.Execution.StoreWF ((stubS s).mapCode V1.Func.toLime) := by
  refine ⟨fun i t m c h => ?_, fun i mi h => hwf.2 i mi h⟩
  have hl : ((stubS s).mapCode V1.Func.toLime).funcs.length =
      (s.mapCode V1.Func.toLime).funcs.length := by
    simp [stubS, Execution.Runtime.Store.mapCode]
  intro a ha
  rw [hl]
  simp only [stubS, Execution.Runtime.Store.mapCode, List.getElem?_map, List.map_map,
    Option.map_eq_some_iff, Function.comp_apply] at h
  obtain ⟨fi, hfi, he⟩ := h
  cases fi with
  | wasm t' m' fn' =>
    simp only [stubF, FuncInst.mapCode, FuncInst.wasm.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hwf.1 i t' m' (V1.Func.toLime fn')
      (by simp [Execution.Runtime.Store.mapCode, hfi, FuncInst.mapCode]) a ha
  | host t' h' =>
    simp only [stubF, FuncInst.mapCode, FuncInst.wasm.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp [stubMod] at ha

/-! ## The forward run at stores with host functions -/

/-- **`Task.wholeRunFwd10Inv` at stores with host functions, through the stub**: every V1 run
from an invocation that calls no host function (a run under `emptyHost10`; see
`step_empty_or_hostCall`) is, read through the stub, a run of the 1.0 script, from a store whose
Core image is valid. The typing hypothesis is on the stubbed invocation. -/
theorem wholeRunFwd10Stub {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s : Store H}
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 (stubS s) args a))
    (hs : StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps emptyHost10 (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 s args a))) (configV hn (stubC c')) :=
  wholeRunFwd10Inv H hn emptyHost10 nd r (stubS s) args a (stubC c') hc (storeOk_stub hs)
    (invokeOk_stub hinv) (storeWF_stub hwf) (steps_stub h)

/-- **The same in `simEnv10T`** (the `STORE`-corrected script). -/
theorem wholeRunFwd10StubT {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s : Store H}
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 (stubS s) args a))
    (hs : StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps emptyHost10 (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 s args a))) (configV hn (stubC c')) :=
  wholeRunFwd10InvT (host := emptyHost10) hc (storeOk_stub hs) (invokeOk_stub hinv)
    (storeWF_stub hwf) (steps_stub h)

/-- **At every store reached from a base store with host functions**,
with a valid Core image and `StoreWF` of the base store only. -/
theorem wholeRunFwd10StubRH {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s₀ s : Store H}
    (hR : ReachH10 s₀ s) (h₀ : StoreOk (coreStore10 s₀))
    (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 (stubS s) args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps emptyHost10 (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 s args a))) (configV hn (stubC c')) :=
  wholeRunFwd10Stub hc (reachH10_ok hR h₀ hw₀).1 hinv (reachH10_ok hR h₀ hw₀).2 h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10StubRHT {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s₀ s : Store H}
    (hR : ReachH10 s₀ s) (h₀ : StoreOk (coreStore10 s₀))
    (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 (stubS s) args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps emptyHost10 (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 s args a))) (configV hn (stubC c')) :=
  wholeRunFwd10StubT hc (reachH10_ok hR h₀ hw₀).1 hinv (reachH10_ok hR h₀ hw₀).2 h

end Silmaril.Wasm.SpecTec.Sim10.HostStub
