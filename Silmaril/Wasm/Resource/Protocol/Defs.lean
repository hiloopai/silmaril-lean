module

public import Silmaril.Wasm.Spec.Temporal.Defs

@[expose] public section

/-!
# Resource protocols: safety automata over events

A **protocol** over an event type `E` with states `S` is a partial deterministic automaton: an
initial state and a partial transition function `step : S → E → Option S`. A word is
**accepted** when the run never gets stuck (`step = none` is a violation). Accepted words are
closed under prefixes, so a protocol is a safety property (a prefix-closed trace predicate,
the shape of a typestate automaton).

Blame is part of the automaton, not of the logic: a violation by the *environment* is not a
rejection, but a move to an absorbing state accepting everything (in the handle protocols of
`Silmaril.Wasm.Resource.Handle`, the state `none`). A protocol therefore says "the program's events
are allowed as long as the environment's events were".

* `Protocol S E`, `Protocol.run`, `Protocol.Accepts`, the computable `Protocol.acceptsB`.
* `Protocol.comap g`: a protocol on `E'` read through `g : E' → E` (event classification).
* `Protocol.prod`: two protocols run side by side (conjunction).
* `protoLogic Ty A R S`: the per-trace logic of the institution format of `Silmaril.Wasm.Spec`
  whose formulas at an interface `X` are protocols over the events of `X` with states `S`
  (`Models (protoLogic …) S p φ` iff every trace of `p` is accepted).
* `Protocol.toAct`: the action predicate of a protocol (`act` atom): the history extended by
  the event is accepted.

Theorems: `Silmaril.Wasm.Resource.Protocol.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec

/-- A protocol: a partial deterministic automaton over events `E` with states `S`. -/
structure Protocol (S E : Type) where
  /-- The initial state. -/
  init : S
  /-- The transition function; `none` is a violation. -/
  step : S → E → Option S

namespace Protocol

variable {S S' E E' : Type}

/-- The run of a protocol from a state along a word. -/
def run (p : Protocol S E) : S → List E → Option S
  | q, [] => some q
  | q, e :: t => (p.step q e).bind fun q' => p.run q' t

/-- The word is accepted: the run from the initial state never gets stuck. -/
def Accepts (p : Protocol S E) (t : List E) : Prop := (p.run p.init t).isSome

/-- Acceptance as a Boolean, for kernel evaluation. -/
def acceptsB (p : Protocol S E) (t : List E) : Bool := (p.run p.init t).isSome

/-- The protocol read through an event map. -/
def comap (g : E' → E) (p : Protocol S E) : Protocol S E' := ⟨p.init, fun q e => p.step q (g e)⟩

/-- Two protocols side by side: a word is accepted iff both accept it. -/
def prod (p : Protocol S E) (p' : Protocol S' E) : Protocol (S × S') E where
  init := (p.init, p'.init)
  step q e := (p.step q.1 e).bind fun a => (p'.step q.2 e).map fun b => (a, b)

/-- The action predicate of a protocol: the history extended by the event is accepted. -/
def toActPred (p : Protocol S E) (h : List E) (e : E) : Prop := p.Accepts (h ++ [e])

end Protocol

/-- **The protocol logic**: formulas at `X` are protocols over the events of `X` with states
`S`; a trace set satisfies a protocol when every trace is accepted. -/
abbrev protoLogic (Ty A R S : Type) : Logic Ty A R :=
  Logic.ofTrace (fun X => Protocol S (Event A R X)) fun φ t => φ.Accepts t

/-- A protocol as a formula of the action-invariant logic `act`. -/
def Protocol.toAct {Ty A R S : Type} {X : Iface Ty} (p : Protocol S (Event A R X)) :
    PosPred A R X :=
  p.toActPred

end Silmaril.Wasm.Resource
