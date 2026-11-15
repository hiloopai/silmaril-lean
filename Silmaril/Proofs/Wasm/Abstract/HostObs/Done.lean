module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms

/-!
# The finished half of the host-observation square (proofs)

Between Core 3.0 invocations with a relational host and the logged closed semantics
`wasmEvFun` (host calls as events), up to a consistent host log:

* `core_done_wasmEv` (backward, deterministic profile; `core_done_wasmEv_profile`, every
  profile under the native side conditions): a stuck end of a typed invocation is blocked
  at a host call (`Pending`), or the end of a logged behaviour with a consistent log;
* `wasmEv_core_done` (forward, every profile): a logged finished behaviour with a
  consistent log is a Core run of the invocation to a stuck end that agrees with it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostObs

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- The exit-flow end of `back_invoke_exit`, as a logged end. -/
theorem coreEnd_of_exit {s₂ : Store H} {fl : Binaryen.Flow} {c : Config H}
    (h : (∃ ws, fl = .normal ws ∧ c = ⟨s₂, {}, vals ws⟩) ∨ (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :
    CoreEnd c (endOfFlow fl s₂) := by
  rcases h with ⟨ws, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact ⟨s₂, rfl⟩

/-- **Backward, finished** (deterministic profile). -/
theorem core_done_wasmEv {o : GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e := by
  rcases back_invoke_exit hT hH hs hS hok hrun hend with hp |
      ⟨fi, ps, rs, s₂, bfl, fl, hfi, hty, hc, hx, he⟩
  · exact .inl hp
  · obtain ⟨cs, hcs, hmem⟩ := hostCall_wasmEv hfi hty hc hx
    exact .inr ⟨cs, _, hcs, hmem, coreEnd_of_exit he⟩

/-- **Backward, finished, every profile**, under the native side conditions. -/
theorem core_done_wasmEv_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e := by
  rcases back_invoke_exit_profile hT hH hN hs hS hW hok hrun hend with hp |
      ⟨fi, ps, rs, s₂, bfl, fl, hfi, hty, hc, hx, he⟩
  · exact .inl hp
  · obtain ⟨cs, hcs, hmem⟩ := hostCall_wasmEv hfi hty hc hx
    exact .inr ⟨cs, _, hcs, hmem, coreEnd_of_exit he⟩

/-- **Forward, finished, every profile**: a logged finished behaviour with a consistent
log is a Core run of the invocation to a stuck end that agrees with it. -/
theorem wasmEv_core_done {P : Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) {cs : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)}
    (h : (cs, e) ∈ wasmEvFun s (a, vs)) (hc : (coreHostRel host).Consistent cs) :
    ∃ c, Steps P host (invoke s a vs) c ∧ (∀ c', ¬ Step P host c c') ∧ CoreEnd c e := by
  obtain ⟨fi, ps, rs, s₂, bfl, fl, hfi, hty, hcall, hx, rfl⟩ := wasmEvFun_hostCall h hc
  have hn : vs.length = ps.length := Interp.args_length hok hfi hty
  obtain ⟨⟨ob, -, hfo, -⟩, hv, ht⟩ :=
    Interp.hostCall_sound (P := P) hH s s₂ {} a fi ps rs vs bfl hS hfi hty hn hcall
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  rw [hinv]
  rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | t
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    exact ⟨_, hv ws rfl, fun _ => Step.not_vals, rfl⟩
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    exact ⟨_, hv ws rfl, fun _ => Step.not_vals, rfl⟩
  · simp [exitFlow] at hx
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    exact ⟨_, hv ws rfl, fun _ => Step.not_vals, rfl⟩
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    exact ⟨_, ht rfl, fun _ => trap_stuck, s₂, rfl⟩
  · exact hfo.elim

end Silmaril.Proofs.Wasm.Abstract.HostObs
