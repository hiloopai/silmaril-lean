module

public import Silmaril.Wasm.Game.Strategy.Defs
public import Silmaril.Games.Composition.Defs

/-!
# Environments and strategy-definable hosts

## Environments

An environment `K : Env E` over the import signature `E` answers each import
question independently: `K e = some w` answers `e` with `w`, `K e = none`
never answers (the host call diverges). Its strategy
`K.strategy : Strategy Sig.empty E` (with empty lower signature, an object of
the game category) is the strategy of a two-state transition system: idle, or
waiting to answer a question. The strategies of this form are the stateless
deterministic strategies over the empty signature; they are exactly what Core's
host relations can express (`Silmaril.Wasm.Game.Env.Thms`): `HostSemantics` has no
host-side state, so a host cannot remember earlier calls. A general (stateful
or nondeterministic) strategy `Strategy Sig.empty E` therefore has no induced
host; it is handled by `Silmaril.Wasm.Game.StatefulEnv`, with a host state machine
in product with Core reduction.

## Strategy-definable hosts

`hostOf ts K` is the host relation induced by `K`: a call of import `h` on
typed arguments returns `K`'s answer as a Core result (an exception answer
`throw a` is the Core result `throw a`) **without changing the store**, or
diverges when `K` gives none. Ill-typed calls and out-of-range imports have no
outcome (they are excluded by well-formedness).

## Composition with an environment

`I.closedWith P s K = K.strategy ≫ I.strategy P s : Strategy Sig.empty I.F` is
the closed program obtained by plugging the environment below the instance.
`Responds C f w` says that the closed strategy `C` answers the question `f`
with `w`; `compositeObs C f` collects the Core behaviours of its answers, and
`diverges` when there is none (divergence is the absence of an answer);
`compositeObsAfter C h f` does the same after a history `h`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- An environment over `E`: a partial answer function (`none`: never answers). -/
def Env (E : Sig.{0}) : Type := (e : E.Op) → Option (E.Ar e)

namespace Env

variable {E : Sig.{0}}

/-- `K` answers the question `e` with `w`. -/
def Answers (K : Env E) (e : E.Op) (w : E.Ar e) : Prop := K e = some w

/-- The events `u` at the interface `E` agree with `K`: questions and answers alternate,
every answer is `K`'s answer, and a last question may be pending. -/
inductive Agrees (K : Env E) : List (Ev E) → Prop where
  /-- Nothing happened. -/
  | nil : Agrees K []
  /-- A last question is pending. -/
  | pending (e : E.Op) : Agrees K [.ask e]
  /-- A question answered as `K` answers it, and more. -/
  | answered {e : E.Op} {w : E.Ar e} {rest : List (Ev E)} :
      K.Answers e w → Agrees K rest → Agrees K (.ask e :: .ans e w :: rest)

/-- Transitions of the transition system of an environment: `none` is idle, `some e`
waits to answer `e`. -/
inductive Step (K : Env E) : Option E.Op → Option (Move Sig.empty E) → Option E.Op → Prop
  /-- Accept a question. -/
  | ask (e : E.Op) : Step K none (some (.inr (.ask e))) (some e)
  /-- Answer it as `K` does. -/
  | ans {e : E.Op} {w : E.Ar e} : K.Answers e w → Step K (some e) (some (.inr (.ans e w))) none

/-- The transition system of an environment. -/
def lts (K : Env E) : LTS Sig.empty E := ⟨Option E.Op, none, K.Step⟩

/-- The strategy of an environment. -/
def strategy (K : Env E) : Strategy Sig.empty E := Strategy.ofLTS K.lts

/-- The environment that never answers. -/
def silent (E : Sig.{0}) : Env E := fun _ => none

end Env

/-- The host relation induced by an environment `K` over the interface `ts`: import `h`
called on typed arguments returns `K`'s answer (as a Core result, exceptions included) and
leaves the store unchanged, or diverges when `K` never answers. -/
def hostOf (ts : List FnType) (K : Env (ifaceSig ts)) : HostSemantics Nat :=
  fun h s args out =>
    ∃ e, ifaceOp? ts h args = some e ∧
      ((∃ w, K.Answers e w ∧ out = .returned s (Answer.toResult (ft := ts.get e.1) w)) ∨
        ((∀ w, ¬ K.Answers e w) ∧ out = .diverged))

/-- The environment `K` throws only exceptions with addresses below `n`. -/
def ThrowsBelow {ts : List FnType} (K : Env (ifaceSig ts)) (n : Nat) : Prop :=
  ∀ e w, K.Answers e w → Answer.ThrowsBelow (ft := ts.get e.1) n w

/-- A host relation is strategy-definable over `ts` when it is induced by an environment. -/
def IsStrategyHost (ts : List FnType) (host : HostSemantics Nat) : Prop :=
  ∃ K : Env (ifaceSig ts), host = hostOf ts K

/-- The core host that diverges on every call. -/
def divHost : HostSemantics Nat := fun _ _ _ out => out = .diverged

/-- The closed strategy `C` answers the question `f` with `w`. -/
def Responds {F : Sig.{0}} (C : Strategy Sig.empty F) (f : F.Op) (w : F.Ar f) : Prop :=
  [.inr (.ask f), .inr (.ans f w)] ∈ C

/-- The observations of a closed strategy `C` for the question `f`: the Core behaviours of
its answers, and `diverges` when it never answers. -/
def compositeObs {ts : List FnType} (C : Strategy Sig.empty (ifaceSig ts))
    (f : (ifaceSig ts).Op) : Set (Silmaril.Wasm.Behaviour Val) :=
  {b | ∃ w, Responds C f w ∧ b = Answer.toBehaviour (ft := ts.get f.1) w} ∪
    {b | b = .diverges ∧ ∀ w, ¬ Responds C f w}

/-- The observations of a closed strategy `C` for the question `f` after the history `h`. -/
def compositeObsAfter {ts : List FnType} (C : Strategy Sig.empty (ifaceSig ts))
    (h : List (Move Sig.empty (ifaceSig ts))) (f : (ifaceSig ts).Op) :
    Set (Silmaril.Wasm.Behaviour Val) :=
  {b | ∃ w, h ++ [.inr (.ask f), .inr (.ans f w)] ∈ C ∧
      b = Answer.toBehaviour (ft := ts.get f.1) w} ∪
    {b | b = .diverges ∧ ∀ w, h ++ [.inr (.ask f), .inr (.ans f w)] ∉ C}

namespace ScalarInstance

variable (I : ScalarInstance)

/-- The closed program of the instance at store `s` against the environment `K`:
`K.strategy ≫ I.strategy P s`. -/
noncomputable def closedWith (P : Profile) (s : Store Nat) (K : Env I.E) :
    Strategy Sig.empty I.F :=
  K.strategy.comp (I.strategy P s)

end ScalarInstance

end Silmaril.Wasm.Game
