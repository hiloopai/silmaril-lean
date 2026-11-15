module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms
import Silmaril.Proofs.Wasm.Abstract.HostObs.Done

/-!
# Core 3.0 invocations against the logged closed semantics with host calls: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostObs`.

**The finished half of the host-observation square.** Between Core 3.0 invocations
with a relational host and the logged closed semantics `wasmEvFun` (host calls as
events, `Silmaril.Wasm.Abstract.HostClosing`), up to a log consistent with the host
(`(coreHostRel host).Consistent`), for typed invocations of checked stores and hosts
with typed answers in the native host slice:

* `core_done_wasmEv` (deterministic profile) and `core_done_wasmEv_profile` (every
  profile, for native-profile Wasm functions and an `Interp.HostNative` host): a stuck
  end of a Core run of the invocation is blocked at a host call (`Pending`), or agrees
  (`CoreEnd`) with a finished logged behaviour with a consistent log;
* `wasmEv_core_done` (every profile): a finished logged behaviour with a consistent log
  is a Core run of the invocation to a stuck end that agrees with it.

The pending (`blocked`) and divergent (`hostDiv`) halves go through `wasmEvPend` and
the forward reach `invoke_pendO_blocked`/`invoke_pendO_diverges`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type} {host : HostSemantics H}

/-- **Backward, finished** (deterministic profile): a stuck end of a typed invocation is
blocked, or the end of a logged behaviour with a consistent host log. -/
theorem core_done_wasmEv {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (SingleThreaded.profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_done_wasmEv hT hH hs hS hok hrun hend

/-- **Backward, finished, every profile**, for native-profile Wasm functions and an
`Interp.HostNative` host. -/
theorem core_done_wasmEv_profile {P : Silmaril.Wasm.Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_done_wasmEv_profile hT hH hN hs hS hW hok hrun hend

/-- **Forward, finished, every profile**: a finished logged behaviour with a consistent
host log is a Core run of the invocation to a stuck end that agrees with it. -/
theorem wasmEv_core_done {P : Silmaril.Wasm.Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) {cs : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)}
    (h : (cs, e) ∈ wasmEvFun s (a, vs)) (hc : (coreHostRel host).Consistent cs) :
    ∃ c, Steps P host (invoke s a vs) c ∧ (∀ c', ¬ Step P host c c') ∧ CoreEnd c e :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.wasmEv_core_done hH hS hok h hc

end Silmaril.Wasm.Abstract
