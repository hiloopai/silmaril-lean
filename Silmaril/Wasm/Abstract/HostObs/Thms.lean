module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms
public import Silmaril.Wasm.Abstract.DivO.Thms
import Silmaril.Proofs.Wasm.Abstract.HostObs.Done
import Silmaril.Proofs.Wasm.Abstract.HostObs.Pend
import Silmaril.Proofs.Wasm.Abstract.HostObs.Back
import Silmaril.Proofs.Wasm.Abstract.HostObs.Square
import Silmaril.Proofs.Wasm.Abstract.HostObs.Div

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

**The pending halves, forward** (every profile): a pending host call of the logged
semantics after a consistent log (`wasmEvPend`) is reached by Core.

* `wasmEvPend_core_blocked`: if the host has no outcome for it, Core runs to a stuck
  end blocked at a host call (`Pending`), the `blocked` observation;
* `wasmEvPend_core_diverges`: if the host may diverge on it, Core diverges, the
  `hostDiv` observation.

**Every stuck end, backward** (`core_stuck_wasmEv`, deterministic profile;
`core_stuck_wasmEv_profile`, every profile under the native side conditions): a stuck
end `c` of a Core run of a typed invocation is blocked at a host call
`(hh, c.store, us)` the host has no outcome for, a pending call of `wasmEvPend` after a
consistent log with `c` at that call (`AtCall`); or it agrees (`CoreEnd`) with a
finished `wasmEvFun` behaviour after a consistent log. From `back_invoke_reach`.

**The host-observation square** (`wasmHostObs`, the `HostRun.hostObs` observations of
the invocation against `coreHostRel host`):

* `wasmHostObs_sound` (every profile): every observation is its Core behaviour
  (`CoreObs`): `done` a run to an agreeing stuck end, `hostDiv` Core divergence,
  `blocked` a run to a stuck end blocked at a host call;
* `core_stuck_wasmHostObs` (deterministic profile) and `core_stuck_wasmHostObs_profile`
  (every profile, native side conditions): every stuck end of a Core run of the
  invocation is a `done` observation it agrees with, or a `blocked` observation at the
  host call it is at.

**Divergence, backward** (`core_div_wasmHostObs`, deterministic profile): a divergent
Core run of the invocation is a `hostDiv` observation of `wasmHostObs`, or diverges
natively: local divergence (`LocalCallDivO (hostCall host)`) after a finite descent, or an
infinite descent chain. These two are not observations of `wasmHostObs`, whose closing
omits divergence; linking them to a logged, host-independent divergent closing is open.
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

/-- **Forward, blocked** (every profile): a logged pending host call with no host
outcome is a Core run of the invocation to a stuck, blocked end. -/
theorem wasmEvPend_core_blocked {P : Silmaril.Wasm.Numerics.Profile}
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {hh : H} {s' : Store H} {us : List Val}
    (h : (cs, (hh, s', us)) ∈ wasmEvPend s (a, vs)) (hc : (coreHostRel host).Consistent cs)
    (hno : ∀ o, ¬ host hh s' us o) :
    ∃ c : Config H, Steps P host (invoke s a vs) c ∧ Pending host c.store c.code ∧
      ∀ c', ¬ Step P host c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.wasmEvPend_core_blocked hH hS hok h hc hno

/-- **Forward, host divergence** (every profile): a logged pending host call the host may
diverge on makes Core diverge. -/
theorem wasmEvPend_core_diverges {P : Silmaril.Wasm.Numerics.Profile}
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {hh : H} {s' : Store H} {us : List Val}
    (h : (cs, (hh, s', us)) ∈ wasmEvPend s (a, vs)) (hc : (coreHostRel host).Consistent cs)
    (hdiv : host hh s' us .diverged) : Diverges P host (invoke s a vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.wasmEvPend_core_diverges hH hS hok h hc hdiv

/-- **Every stuck end of a typed invocation is a logged observation** (deterministic
profile): blocked at a logged pending host call, or a finished logged behaviour. -/
theorem core_stuck_wasmEv {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (SingleThreaded.profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    (∃ (hh : H) (a' : Nat) (us : List Val) (cs : List (Call (wasmHostSig H))),
      (coreHostRel host).Consistent cs ∧ (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) ∧
      (∀ o, ¬ host hh c.store us o) ∧ AtCall c.store a' us c.code) ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_stuck_wasmEv hT hH hs hS hok hrun hend

/-- **`core_stuck_wasmEv` at every profile**, for native-profile Wasm functions and an
`Interp.HostNative` host. -/
theorem core_stuck_wasmEv_profile {P : Silmaril.Wasm.Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    (∃ (hh : H) (a' : Nat) (us : List Val) (cs : List (Call (wasmHostSig H))),
      (coreHostRel host).Consistent cs ∧ (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) ∧
      (∀ o, ¬ host hh c.store us o) ∧ AtCall c.store a' us c.code) ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_stuck_wasmEv_profile hT hH hN hs hS hW hok hrun hend

/-- **Soundness of the host observations** (every profile): every observation of the
invocation against `coreHostRel host` is its Core behaviour. -/
theorem wasmHostObs_sound {P : Silmaril.Wasm.Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) {o : HObs (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : o ∈ wasmHostObs host s a vs) : CoreObs P host s a vs o :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.wasmHostObs_sound hH hS hok h

/-- **Completeness of the host observations for stuck ends** (deterministic profile). -/
theorem core_stuck_wasmHostObs {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (SingleThreaded.profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    (∃ cs e, HObs.done cs e ∈ wasmHostObs host s a vs ∧ CoreEnd c e) ∨
      ∃ (cs : List (Call (wasmHostSig H))) (hh : H) (a' : Nat) (us : List Val),
        HObs.blocked cs (hh, c.store, us) ∈ wasmHostObs host s a vs ∧
        AtCall c.store a' us c.code :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_stuck_wasmHostObs hT hH hs hS hok hrun hend

/-- **Completeness for stuck ends, every profile**, for native-profile Wasm functions and an
`Interp.HostNative` host. -/
theorem core_stuck_wasmHostObs_profile {P : Silmaril.Wasm.Numerics.Profile}
    (hT : HostTyped host) (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host)
    {n : Nat} {s : Store H} {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    (∃ cs e, HObs.done cs e ∈ wasmHostObs host s a vs ∧ CoreEnd c e) ∨
      ∃ (cs : List (Call (wasmHostSig H))) (hh : H) (a' : Nat) (us : List Val),
        HObs.blocked cs (hh, c.store, us) ∈ wasmHostObs host s a vs ∧
        AtCall c.store a' us c.code :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_stuck_wasmHostObs_profile hT hH hN hs hS hW hok
    hrun hend

/-- **Every Core divergence of a typed invocation is a `hostDiv` observation, or native
divergence** (deterministic profile). -/
theorem core_div_wasmHostObs {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hd : Diverges (SingleThreaded.profile o) host (invoke s a vs)) :
    (∃ (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op),
        HObs.hostDiv cs m ∈ wasmHostObs host s a vs) ∨
      (∃ z, (z = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ z) ∧
        LocalCallDivO (hostCall host) z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
        ∀ n, BodyReachO (hostCall host) (g n) (g (n + 1)) :=
  Silmaril.Proofs.Wasm.Abstract.HostObs.core_div_wasmHostObs hT hH hs hS hok hd

end Silmaril.Wasm.Abstract
