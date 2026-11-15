module

public import Silmaril.Proofs.Wasm.Abstract.HostObs.Done
public import Silmaril.Proofs.Wasm.Abstract.HostObs.Pend
public import Silmaril.Proofs.Wasm.Abstract.HostObs.Back

/-!
# The host-observation square (proofs)

The observations `wasmHostObs host s a vs` of an invocation against the relational host
`coreHostRel host` (`HostRun.hostObs` of the logged closed semantics) and Core 3.0:

* `wasmHostObs_sound` (every profile): every observation is its Core behaviour
  (`CoreObs`): `done` a run to an agreeing stuck end, `hostDiv` Core divergence,
  `blocked` a run to a stuck end blocked at a host call;
* `core_stuck_wasmHostObs` (deterministic profile; `_profile`, every profile under the
  native side conditions): every stuck end of a Core run of the invocation is a `done`
  observation it agrees with, or a `blocked` observation at the host call it is at.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostObs

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

theorem noOutcome_iff {hh : H} {s : Store H} {us : List Val} :
    (∀ ans, ¬ coreHostRel host (hh, s, us) ans) ↔ ∀ o, ¬ host hh s us o := by
  constructor
  · intro h o ho
    cases o with
    | returned s' r => exact h (.answer (s', r)) ho
    | diverged => exact h .diverge ho
  · intro h ans ha
    cases ans with
    | answer p => exact h _ ha
    | diverge => exact h _ ha

/-- **Soundness of the observations** (every profile). -/
theorem wasmHostObs_sound {P : Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) {o : HObs (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : o ∈ wasmHostObs host s a vs) : CoreObs P host s a vs o := by
  rcases h with ⟨cs, e, rfl, hm, hc⟩ | ⟨cs, ⟨hh, s', us⟩, rfl, hm, hc, hd⟩ |
      ⟨cs, ⟨hh, s', us⟩, rfl, hm, hc, hno⟩
  · exact wasmEv_core_done hH hS hok hm hc
  · exact wasmEvPend_core_diverges hH hS hok hm hc hd
  · exact wasmEvPend_core_blocked hH hS hok hm hc (noOutcome_iff.mp hno)

/-- A stuck end classified by `core_stuck_wasmEv`, as an observation. -/
theorem obs_of_stuck {s : Store H} {a : Nat} {vs : List Val} {c : Config H}
    (h : (∃ (hh : H) (a' : Nat) (us : List Val) (cs : List (Call (wasmHostSig H))),
      (coreHostRel host).Consistent cs ∧ (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) ∧
      (∀ o, ¬ host hh c.store us o) ∧ AtCall c.store a' us c.code) ∨
      ∃ cs e, (coreHostRel host).Consistent cs ∧ (cs, e) ∈ wasmEvFun s (a, vs) ∧ CoreEnd c e) :
    (∃ cs e, HObs.done cs e ∈ wasmHostObs host s a vs ∧ CoreEnd c e) ∨
      ∃ (cs : List (Call (wasmHostSig H))) (hh : H) (a' : Nat) (us : List Val),
        HObs.blocked cs (hh, c.store, us) ∈ wasmHostObs host s a vs ∧
        AtCall c.store a' us c.code := by
  rcases h with ⟨hh, a', us, cs, hc, hm, hno, hat⟩ | ⟨cs, e, hc, hm, he⟩
  · exact .inr ⟨cs, hh, a', us, .inr (.inr ⟨cs, _, rfl, hm, hc, noOutcome_iff.mpr hno⟩), hat⟩
  · exact .inl ⟨cs, e, .inl ⟨cs, e, rfl, hm, hc⟩, he⟩

/-- **Completeness for stuck ends** (deterministic profile). -/
theorem core_stuck_wasmHostObs {o : GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    (∃ cs e, HObs.done cs e ∈ wasmHostObs host s a vs ∧ CoreEnd c e) ∨
      ∃ (cs : List (Call (wasmHostSig H))) (hh : H) (a' : Nat) (us : List Val),
        HObs.blocked cs (hh, c.store, us) ∈ wasmHostObs host s a vs ∧
        AtCall c.store a' us c.code :=
  obs_of_stuck (core_stuck_wasmEv hT hH hs hS hok hrun hend)

/-- **Completeness for stuck ends, every profile**, under the native side conditions. -/
theorem core_stuck_wasmHostObs_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    (∃ cs e, HObs.done cs e ∈ wasmHostObs host s a vs ∧ CoreEnd c e) ∨
      ∃ (cs : List (Call (wasmHostSig H))) (hh : H) (a' : Nat) (us : List Val),
        HObs.blocked cs (hh, c.store, us) ∈ wasmHostObs host s a vs ∧
        AtCall c.store a' us c.code :=
  obs_of_stuck (core_stuck_wasmEv_profile hT hH hN hs hS hW hok hrun hend)

end Silmaril.Proofs.Wasm.Abstract.HostObs
