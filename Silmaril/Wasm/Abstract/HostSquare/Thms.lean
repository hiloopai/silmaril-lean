module

public import Silmaril.Wasm.Abstract.HostSquare.Defs
public import Silmaril.Wasm.Abstract.HostObs.Thms
public import Silmaril.Wasm.Abstract.HostClosingInf.Thms
import Silmaril.Proofs.Wasm.Abstract.HostSquare.Basic

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

end Silmaril.Wasm.Abstract
