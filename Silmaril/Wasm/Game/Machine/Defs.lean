module

public import Silmaril.Wasm.Game.Signature.Defs
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.Determinism
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

/-!
# Host-free runs of the single-threaded machine

The strategy of a Core 3.0 instance (`Silmaril.Wasm.Game.Strategy`) is read off
silmaril-lean's single-threaded machine `Silmaril.Wasm.SingleThreaded`
(`Thread`, `Internal`, `decompose?`, `resumeResult`). This module names the
machine-level predicates the strategy uses:

* `CalloutAt s t h args`: the thread is stopped at the host-call redex found
  by `decompose?` (the machine's `status` is `.callout h args`);
* `ResultAt s t r`: the thread has finished with the Core result `r` (values,
  trap, or an uncaught exception `throw a`);
* `InternalP P`: the host-free step of the machine under an **arbitrary**
  silmaril profile `P` (any `$ND`, relaxed choices, NaN policy and grow
  policy); silmaril-lean's `Internal o` is the instance `P = profile o`
  (`internalP_profile`). `statusP P` is `status` with `InternalP P`;
* `Reach P`: host-free runs (`InternalP P`). The relation is not
  functional in general (NaN payloads, relaxed operators, grow failure);
* `answerHost h args r`: the host answering exactly the call `h args` with
  `r`, used to read an environment answer as one Core step.

Their properties (agreement with Core reduction for every profile, uniqueness
of normal forms for the deterministic profiles `profile o`) are in
`Silmaril.Wasm.Game.Machine.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- The internal (host-free) step of the single-threaded machine under the profile `P`: a
Core step with the empty host relation, landing in an active thread. For `P = profile o` this
is silmaril-lean's `Internal o` (`internalP_profile`). -/
def InternalP {H : Type} (P : Profile) (x y : Store H × Thread) : Prop :=
  ∃ f' code', y.2 = .active f' code' ∧
    Step P (fun _ _ _ _ => False) (x.2.config x.1) ⟨y.1, f', code'⟩

open Classical in
/-- The status of a thread under the profile `P` (silmaril-lean's `status` with
`InternalP P`). -/
noncomputable def statusP {H : Type} (P : Profile) (s : Store H) (t : Thread) : Status H :=
  let c := t.config s
  if h : ∃ vs, c.code = vals vs then .returned (.values h.choose)
  else if c.code = [.trap] then .returned .trap
  else if ∃ a, c.code = throwing a then .returned .trap
  else match decompose? s c.code with
    | some (_, _, h, args) => .callout h args
    | none => if ∃ y, InternalP P (s, t) y then .running else .stuck

/-- The thread `t` in store `s` is stopped at a host callout `h args` (the redex found by
`decompose?`, i.e. `Status.callout h args`). -/
def CalloutAt (s : Store Nat) (t : Thread) (h : Nat) (args : List Val) : Prop :=
  ∃ E a, decompose? s (t.config s).code = some (E, a, h, args)

/-- The thread `t` in store `s` has finished with the Core result `r`. -/
def ResultAt (s : Store Nat) (t : Thread) (r : Result) : Prop :=
  (t.config s).code = r.toAdmin

/-- Host-free runs of the single-threaded machine under the profile `P`. -/
abbrev Reach (P : Profile) : Store Nat × Thread → Store Nat × Thread → Prop :=
  Relation.ReflTransGen (InternalP P)

/-- The host relation answering exactly the call `h args` with `r`, leaving the store
unchanged: the oracle that replays one environment answer. -/
def answerHost (h : Nat) (args : List Val) (r : Result) : HostSemantics Nat :=
  fun h' s vs out => h' = h ∧ vs = args ∧ out = .returned s r

end Silmaril.Wasm.Game
