module

public import Silmaril.Wasm.Abstract.HostSquare.Defs
public import Silmaril.Wasm.Abstract.HostObs.Thms
public import Silmaril.Wasm.Abstract.HostClosingInf.Thms
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Abstract.HostSquare.Basic
import Silmaril.Proofs.Wasm.Abstract.HostSquare.Profile

/-!
# The exact-log commuting square for host calls (stage H2): theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostSquare`. Deterministic profile `profile o`, typed
checked invocations (`StoreOk s`, `Interp.StoreChk s.funcs`, `InvokeOk s a vs`) and a host with
typed answers in the native host slice (`HostTyped host`, `Interp.NativeHostSlice host`):

* `hostSquare` (**the square**): every observation `x : FullObs H` is native (`NatObs`) exactly
  when it is a Core observation at exactly its log (`CoreObsL`). Case by case:
  `wasmEvFun_vals_iff` and `wasmEvFun_trap_iff` (`done`, a trap erasing its store),
  `wasmEvPend_evRun` and `evRun_pend` (`blocked`, `hostDiv`), `wasmEvFunD_div_iff` (`div`),
  `hostObsInf_wasmEvInf_eq` and `wasmEvInf_hostObsInf` (`prod`). A finished end that is a
  thrown exception (`ret (inr t)`) or `div` is on neither side: natively, its Core end would
  agree with it (`wasmEv_core_done`), and no Core end does;
* `hostSquare_stuck`: every stuck end of a Core run of the invocation is a `done` observation
  it agrees with (`CoreEnd`), or a `blocked` observation at the host call it is at, both at the
  run's own log;
* `hostSquare_diverges`: every divergence of the invocation is a `div` observation (quiescent,
  host-free divergence after a log), a `hostDiv` observation (a host-free run after a log to a
  host call the host diverges on) or a `prod` observation (infinitely many host events), from
  `diverges_events` and `quiet_iff`;
* `hostSquare_cover` (**completeness**): every Core run of the invocation extends to a stuck
  end (`hostSquare_stuck`) or diverges (`hostSquare_diverges`), so is a finite prefix of an
  observation of the square.

**Every profile** `P`, for a store whose Wasm functions are native-profile code
(`Interp.NativeWasmFuncs s.funcs`) and a host satisfying the explicit side condition
`Interp.HostNative host` (its answers keep that, and never throw). Every configuration reached
from the invocation is then `Interp.NHConfig`, where Core steps do not depend on the profile:

* `hEvStep_profile`, `evRun_profile`, `quietSteps_profile`, `diverges_noHost_profile`,
  `coreInf_profile`: labelled steps from native code, and labelled runs, event-free runs,
  host-free divergence and productive runs from `NHConfig` configurations, transfer between
  profiles. A labelled step needs only `NAdmins`; host-free divergence needs no `HostNative`
  (the host `fun _ _ _ _ => False` satisfies it, `hostNative_noHost`);
* `coreObsL_profile`: the Core observations of an invocation are the same at every profile;
* `hostSquare_profile`, `hostSquare_cover_profile`: the square and its completeness at every
  profile.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {host : HostSemantics H}

/-- No answer of the relational host `coreHostRel host` is no outcome of `host`. -/
theorem coreHostRel_noAns_iff {m : (wasmHostSig H).Op} :
    (∀ ans, ¬ coreHostRel host m ans) ↔ ∀ o, ¬ host m.1 m.2.1 m.2.2 o :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.noAns_iff

/-- **The exact-log commuting square** (deterministic profile `profile o`, typed checked
invocations, a host with typed answers in the native host slice): an observation is native
exactly when it is a Core observation at exactly its log. -/
theorem hostSquare {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) (x : FullObs H) :
    NatObs host s a vs x ↔ CoreObsL (SingleThreaded.profile o) host s a vs x :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostSquare hT hH hs hS hok x

/-- **Every stuck end is an observation of the square**, at the run's own log: a `done`
observation it agrees with, or a `blocked` observation at the host call it is at. -/
theorem hostSquare_stuck {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) {c : Config H}
    (hrun : Steps (SingleThreaded.profile o) host (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    ∃ cs, EvRun (SingleThreaded.profile o) host (invoke s a vs) cs c ∧
      ((∃ e, NatObs host s a vs (.done cs e) ∧ CoreEnd c e) ∨
        ∃ (hh : H) (us : List Val), NatObs host s a vs (.blocked cs (hh, c.store, us)) ∧
          ∃ (E : SingleThreaded.Ctx) (a' : Nat),
            SingleThreaded.decompose? c.store c.code = some (E, a', hh, us)) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostSquare_stuck hT hH hs hS hok hrun hend

/-- **Every divergence is an observation of the square**: `div`, `hostDiv` or `prod`. -/
theorem hostSquare_diverges {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hd : Diverges (SingleThreaded.profile o) host (invoke s a vs)) :
    (∃ cs, NatObs host s a vs (.div cs)) ∨ (∃ cs m, NatObs host s a vs (.hostDiv cs m)) ∨
      ∃ ω, NatObs host s a vs (.prod ω) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostSquare_diverges hT hH hs hS hok hd

/-- Every Core run extends to a stuck end, or diverges. -/
theorem steps_stuck_or_diverges {P : Numerics.Profile} {c : Config H} :
    (∃ d, Steps P host c d ∧ ∀ d', ¬ Step P host d d') ∨ Diverges P host c :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.steps_stuck_or_diverges

/-- **Completeness of the square** (deterministic profile `profile o`, typed checked
invocations): every Core run of the invocation is a finite prefix of an observation of the
square. It extends to a stuck end, a `done` or `blocked` observation at the end's own log, or it
diverges, a `div`, `hostDiv` or `prod` observation. -/
theorem hostSquare_cover {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) {c : Config H}
    (hrun : Steps (SingleThreaded.profile o) host (invoke s a vs) c) :
    (∃ (d : Config H) (cs : List (Call (wasmHostSig H))),
      Steps (SingleThreaded.profile o) host c d ∧
      (∀ d', ¬ Step (SingleThreaded.profile o) host d d') ∧
      EvRun (SingleThreaded.profile o) host (invoke s a vs) cs d ∧
      ((∃ e, NatObs host s a vs (.done cs e) ∧ CoreEnd d e) ∨
        ∃ (hh : H) (us : List Val), NatObs host s a vs (.blocked cs (hh, d.store, us)) ∧
          ∃ (E : SingleThreaded.Ctx) (a' : Nat),
            SingleThreaded.decompose? d.store d.code = some (E, a', hh, us))) ∨
      (Diverges (SingleThreaded.profile o) host c ∧
        ((∃ cs, NatObs host s a vs (.div cs)) ∨ (∃ cs m, NatObs host s a vs (.hostDiv cs m)) ∨
          ∃ ω, NatObs host s a vs (.prod ω))) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostSquare_cover hT hH hs hS hok hrun

/-! ## Every profile -/

/-- A labelled step from native-profile code is a labelled step at every profile. -/
theorem hEvStep_profile {P P' : Numerics.Profile} {c c' : Config H}
    {e : Option (Call (wasmHostSig H))} (h : HEvStep P host c e c') (hc : Interp.NAdmins c.code) :
    HEvStep P' host c e c' :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hEvStep_profile h hc

/-- Labelled runs transfer between profiles from a native configuration; the end is native. -/
theorem evRun_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host) {c c' : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') (hc : Interp.NHConfig c) :
    EvRun P' host c cs c' ∧ Interp.NHConfig c' :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.evRun_profile hN h hc

/-- Event-free labelled runs transfer between profiles from a native configuration. -/
theorem quietSteps_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host)
    {c c' : Config H} (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c')
    (hc : Interp.NHConfig c) :
    Relation.ReflTransGen (fun a b => HEvStep P' host a none b) c c' ∧ Interp.NHConfig c' :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.quietSteps_profile hN h hc

/-- The host without outcomes stays in the native profile. -/
theorem hostNative_noHost : Interp.HostNative (fun _ _ _ _ => False : HostSemantics H) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostNative_noHost

/-- Host-free divergence transfers between profiles from a native configuration. -/
theorem diverges_noHost_profile {P P' : Numerics.Profile} {c : Config H}
    (h : Diverges P (fun _ _ _ _ => False) c) (hc : Interp.NHConfig c) :
    Diverges P' (fun _ _ _ _ => False) c :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.diverges_noHost_profile h hc

/-- Productive runs transfer between profiles from a native configuration. -/
theorem coreInf_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host) {c : Config H}
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host c ω) (hc : Interp.NHConfig c) :
    CoreInf P' host c ω :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.coreInf_profile hN h hc

/-- **The Core observations of an invocation are the same at every profile**, for a store with
native-profile Wasm functions and a host satisfying `Interp.HostNative`. -/
theorem coreObsL_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host)
    {s : Store H} {a : Nat} {vs : List Val} (hW : Interp.NativeWasmFuncs s.funcs)
    (x : FullObs H) : CoreObsL P host s a vs x ↔ CoreObsL P' host s a vs x :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.coreObsL_profile hN hW x

/-- **The exact-log commuting square at every profile** (typed checked invocations, a host with
typed answers in the native host slice), for a store with native-profile Wasm functions and a
host satisfying `Interp.HostNative`. -/
theorem hostSquare_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs) (x : FullObs H) :
    NatObs host s a vs x ↔ CoreObsL P host s a vs x :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostSquare_profile hT hH hN hs hS hW hok x

/-- **Completeness of the square at every profile**, for a store with native-profile Wasm
functions and a host satisfying `Interp.HostNative`. -/
theorem hostSquare_cover_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs) {c : Config H}
    (hrun : Steps P host (invoke s a vs) c) :
    (∃ (d : Config H) (cs : List (Call (wasmHostSig H))),
      Steps P host c d ∧ (∀ d', ¬ Step P host d d') ∧ EvRun P host (invoke s a vs) cs d ∧
      ((∃ e, NatObs host s a vs (.done cs e) ∧ CoreEnd d e) ∨
        ∃ (hh : H) (us : List Val), NatObs host s a vs (.blocked cs (hh, d.store, us)) ∧
          ∃ (E : SingleThreaded.Ctx) (a' : Nat),
            SingleThreaded.decompose? d.store d.code = some (E, a', hh, us))) ∨
      (Diverges P host c ∧
        ((∃ cs, NatObs host s a vs (.div cs)) ∨ (∃ cs m, NatObs host s a vs (.hostDiv cs m)) ∨
          ∃ ω, NatObs host s a vs (.prod ω))) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquare.hostSquare_cover_profile hT hH hN hs hS hW hok hrun

end Silmaril.Wasm.Abstract
