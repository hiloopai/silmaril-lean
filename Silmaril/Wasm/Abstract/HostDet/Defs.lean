module

public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# Deterministic hosts and logged Core runs

A Core 3.0 host `host : HostSemantics H` is a relation: a call may have several outcomes, none,
or diverge. Two definitions for hosts that are functions on the calls they answer:

* `HostDet host`: **every host call has at most one outcome** (one store and result, or
  divergence). Answers are not required to exist, and their typing is a separate condition
  (`Silmaril.Wasm.Abstract.HostTyped`).
* `LStep P host`: a Core step that **records the host calls it answers** in a log of
  `(host function, arguments)` pairs: a host-free step keeps the log, an answered host call at the
  configuration's callout (`SingleThreaded.decompose?`, under any label, handler or frame) appends
  its call, and a call the host diverges on stutters with the log unchanged. Its first projection
  is exactly `Step P host` (`LStep.toStep`, `Step.toLStep`, `….Thms`). The log is the observable
  projection of a run that is finer than its final configuration: an embedder can see which host
  functions were called, in which order, with which arguments.

`Silmaril.Wasm.Abstract.HostDet.Thms`: at the deterministic profile `SingleThreaded.profile o`,
with `HostDet host`, `Step` and `LStep` have the one-step diamond of host-free reduction, normal
forms are unique, **and so is the log of a run to a normal form**.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- **A deterministic host**: each call (host function, store, arguments) has at most one
outcome. -/
def HostDet (host : HostSemantics H) : Prop :=
  ∀ (h : H) (s : Store H) (vs : List Val) (o₁ o₂ : HostOutcome H),
    host h s vs o₁ → host h s vs o₂ → o₁ = o₂

/-- A log of answered host calls: the host function and the arguments, oldest first. -/
abbrev HostLog (H : Type) := List (H × List Val)

/-- **A Core step with its host-call log.** -/
inductive LStep (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    Config H × HostLog H → Config H × HostLog H → Prop where
  /-- A host-free step; the log is unchanged. -/
  | free {c c' : Config H} {l : HostLog H} (h : Step P (fun _ _ _ _ => False) c c') :
      LStep P host (c, l) (c', l)
  /-- An answered host call at the callout of `c`: the answer is plugged into the context and the
  call is appended to the log. -/
  | call {c : Config H} {l : HostLog H} {E : Ctx} {a : Nat} {hh : H} {args : List Val}
      {s' : Store H} {r : Result} (hd : decompose? c.store c.code = some (E, a, hh, args))
      (hr : host hh c.store args (.returned s' r)) :
      LStep P host (c, l) (⟨s', c.frame, E.fill r.toAdmin⟩, l ++ [(hh, args)])
  /-- A host call the host diverges on: a stutter, with the log unchanged. -/
  | div {c : Config H} {l : HostLog H} {E : Ctx} {a : Nat} {hh : H} {args : List Val}
      (hd : decompose? c.store c.code = some (E, a, hh, args))
      (hr : host hh c.store args .diverged) : LStep P host (c, l) (c, l)

/-- Runs of `LStep`. -/
abbrev LSteps (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :=
  Relation.ReflTransGen (LStep P host)

end Silmaril.Wasm.Abstract

end
