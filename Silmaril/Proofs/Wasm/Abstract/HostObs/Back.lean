module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms

/-!
# Every stuck end of a Core invocation is a logged observation (proofs)

`core_stuck_wasmEv` (deterministic profile; `core_stuck_wasmEv_profile`, every profile under
the native side conditions): a stuck end `c` of a Core run of a typed invocation is either

* **blocked** at a host call `(hh, c.store, us)` the host has no outcome for, which is a
  pending call of the logged semantics (`wasmEvPend`) after a consistent host log, with
  `c`'s code at that call (`AtCall`); or
* **finished**: it agrees (`CoreEnd`) with a finished logged behaviour (`wasmEvFun`) after a
  consistent host log.

From the reach evidence of `back_invoke_reach` and `wasmEvPend_iff`, and from
`hostCall_wasmEv` through the exit flow.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostObs

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- The answered end of `back_invoke`, as a finished logged behaviour. -/
theorem wasmEv_of_answer {s : Store H} {a : Nat} {vs : List Val} {c : Config H}
    (h : ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H)
        (fl : Binaryen.Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      hostCall host s a vs (s₂, fl) ∧
      ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
        (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩))) :
    ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e := by
  obtain ⟨fi, ps, rs, s₂, fl, hfi, hty, hc, he⟩ := h
  rcases he with ⟨ws, hw, rfl⟩ | ⟨rfl, rfl⟩
  · have hx : exitFlow rs.length fl = some (.normal (ws.take rs.length).reverse) := by
      rcases fl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;>
        simp_all [Binaryen.Flow.retVals, exitFlow]
    obtain ⟨cs, hcs, hmem⟩ := hostCall_wasmEv hfi hty hc hx
    exact ⟨cs, _, hcs, hmem, rfl⟩
  · obtain ⟨cs, hcs, hmem⟩ := hostCall_wasmEv (fl := .trap) hfi hty hc rfl
    exact ⟨cs, _, hcs, hmem, s₂, rfl⟩

/-- The blocked end of `back_invoke_reach`, as a logged pending call. -/
theorem wasmEvPend_of_blocked {s : Store H} {a : Nat} {vs : List Val} {c : Config H}
    (h : ∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧ y.2.2 = c.store ∧
        c.store.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ (∀ o, ¬ host hh c.store y.2.1 o) ∧
        AtCall c.store y.1 y.2.1 c.code) :
    ∃ (hh : H) (a' : Nat) (us : List Val) (cs : List (Call (wasmHostSig H))),
      (coreHostRel host).Consistent cs ∧ (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) ∧
      (∀ o, ¬ host hh c.store us o) ∧ AtCall c.store a' us c.code := by
  obtain ⟨y, fi, hh, hy, hys, hf, hcode, hno, hat⟩ := h
  obtain ⟨cs, hmem, hcs⟩ := (wasmEvPend_iff (host := host) (m := (hh, y.2.2, y.2.1))).mpr
    ⟨y, fi, hh, hy, hys ▸ hf, hcode, rfl⟩
  exact ⟨hh, y.1, y.2.1, cs, hcs, hys ▸ hmem, hno, hat⟩

/-- **Every stuck end of a typed invocation is a logged observation** (deterministic
profile): blocked at a logged pending host call, or a finished logged behaviour. -/
theorem core_stuck_wasmEv {o : GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    (∃ (hh : H) (a' : Nat) (us : List Val) (cs : List (Call (wasmHostSig H))),
      (coreHostRel host).Consistent cs ∧ (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) ∧
      (∀ o, ¬ host hh c.store us o) ∧ AtCall c.store a' us c.code) ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e :=
  (back_invoke_reach hT hH hs hS hok hrun hend).imp wasmEvPend_of_blocked wasmEv_of_answer

/-- **`core_stuck_wasmEv` at every profile**, for native-profile Wasm functions and an
`Interp.HostNative` host. -/
theorem core_stuck_wasmEv_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    (∃ (hh : H) (a' : Nat) (us : List Val) (cs : List (Call (wasmHostSig H))),
      (coreHostRel host).Consistent cs ∧ (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) ∧
      (∀ o, ¬ host hh c.store us o) ∧ AtCall c.store a' us c.code) ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e :=
  (back_invoke_reach_profile hT hH hN hs hS hW hok hrun hend).imp
    wasmEvPend_of_blocked wasmEv_of_answer

end Silmaril.Proofs.Wasm.Abstract.HostObs
