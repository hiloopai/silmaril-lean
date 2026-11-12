module

public import Silmaril.Wasm.Game.Env.Defs
public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Wasm.Behaviour.Semantics.Core

/-!
# Stateful, nondeterministic environments

The environments of `Silmaril.Wasm.Game.Env` are partial answer functions: each
import call is answered independently and deterministically, which is what
silmaril's Core host relations (`HostSemantics`, with no host state) can
express through `hostOf`. This module removes the statelessness and the
determinism.

## Stateful environments

A stateful environment `L : SEnv E` over the import signature `E` is a host
*state machine*, relational in every respect:

* `L.S`: the host states (any type);
* `L.Ans q e w q'`: in state `q` the host may answer the import question `e`
  with `w` and move to `q'` (several answers and successor states allowed);
* `L.Div q e`: in state `q` the host may diverge on `e`. A question with no
  answer in state `q` also diverges (`L.Silent q e`).

Its strategy `L.strategy q : Strategy Sig.empty E` is the strategy of the
transition system with states `L.S × Option E.Op` (idle, or waiting to answer
a question). **Every** environment strategy arises this way:
`(SEnv.ofStrategy τ).strategy [] = τ` for every `τ : Strategy Sig.empty E`
(`Silmaril.Wasm.Game.StatefulEnv.Thms`), the host state being the history of
answered calls. The stateless environments are the one-state machines
`SEnv.ofEnv K`.

## The operational semantics with a stateful host

Core's host relation has no host state, so the closed-world semantics is the
**product** of Core reduction with the host state machine, on pairs
`(c, q) : Config Nat × L.S` (`SStep P L`):

* `internal`: a Core step under the empty host (`Step P (fun _ _ _ _ => False)`,
  any profile `P`); the host state is unchanged;
* `answer`: the configuration is at the host-call redex `h args` found by
  `decompose?`, which is the typed import call `e` (`ifaceOp?`); the host
  answers `w` and moves to `q'`, and the code continues with the Core result
  `w.toResult` in the same store (Core's `callRefHost` reduct);
* `silent`: the host diverges on that call: a self-loop, Core's
  `callRefHostDiv` reduct.

Each product step is a Core step against the stateless host `L.hostAt q` of
the current state, and conversely (`SStep.core_step`, `core_step_sstep`); for
the one-state machine `ofEnv K` the product semantics is Core reduction under
`hostOf ts K`. `sbehavioursOf P L q c` are the behaviours of `c` with the host
in state `q`: Core results of finite product runs and `diverges` for infinite
product runs, exactly as silmaril's `behavioursOf`.

## Divergence read off the game

`L.dlts q` is the transition system of `L` with a silent self-loop on a
question that `L` may leave unanswered (`L.Silent`), and
`L.dstrategy q = DStrategy.ofLTS (L.dlts q)` its divergence-observing
strategy. The closed program as a divergence-observing strategy is the
composite `I.closedSD P s L q = (L.dstrategy q).comp (I.dstrategy P s)` of
`Silmaril.Games.DivComp`; its divergent plays after an export question are the
infinite product runs (`Silmaril.Wasm.Game.StatefulEnv.Thms`).

## The restriction that remains

The host does not change the Wasm store: an answer is a value list, a trap or
an exception address (`Answer`), and the store is not part of the game
interface. A host that writes the module's memory or tables needs the store
(or the shared part of it) in the signature; see `docs/projects/games.md`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- A stateful, nondeterministic environment over `E`: a host state machine. -/
structure SEnv (E : Sig.{0}) where
  /-- Host states. -/
  S : Type
  /-- `Ans q e w q'`: in state `q` the host may answer `e` with `w`, moving to `q'`. -/
  Ans : S → (e : E.Op) → E.Ar e → S → Prop
  /-- `Div q e`: in state `q` the host may diverge on `e`. -/
  Div : S → E.Op → Prop

namespace SEnv

variable {E : Sig.{0}} (L : SEnv E)

/-- The host diverges on `e` in state `q`: it may diverge, or it has no answer. -/
def Silent (q : L.S) (e : E.Op) : Prop := L.Div q e ∨ ∀ w q', ¬ L.Ans q e w q'

/-- The events `u` at the interface `E` agree with `L` from state `q`: questions and answers
alternate, every answer is an answer of `L` from the state reached so far, and a last
question may be pending. -/
inductive Agrees : L.S → List (Ev E) → Prop where
  /-- Nothing happened. -/
  | nil (q : L.S) : Agrees q []
  /-- A last question is pending. -/
  | pending (q : L.S) (e : E.Op) : Agrees q [.ask e]
  /-- A question answered as `L` may answer it, and more from the new state. -/
  | answered {q q' : L.S} {e : E.Op} {w : E.Ar e} {rest : List (Ev E)} :
      L.Ans q e w q' → Agrees q' rest → Agrees q (.ask e :: .ans e w :: rest)

/-- `Drive q u q'`: the complete exchange `u` (answered calls only) is a run of `L` from `q`
to `q'`. -/
inductive Drive : L.S → List (Ev E) → L.S → Prop where
  /-- No call. -/
  | nil (q : L.S) : Drive q [] q
  /-- An answered call, and more. -/
  | cons {q q' q'' : L.S} {e : E.Op} {w : E.Ar e} {u : List (Ev E)} :
      L.Ans q e w q' → Drive q' u q'' → Drive q (.ask e :: .ans e w :: u) q''

/-- Transitions of the transition system of `L`: `(q, none)` is idle in host state `q`,
`(q, some e)` waits to answer `e`. -/
inductive Trans : L.S × Option E.Op → Option (Move Sig.empty E) → L.S × Option E.Op → Prop
  /-- Accept a question. -/
  | ask (q : L.S) (e : E.Op) : Trans (q, none) (some (.inr (.ask e))) (q, some e)
  /-- Answer it as `L` may, moving to the new state. -/
  | ans {q q' : L.S} {e : E.Op} {w : E.Ar e} :
      L.Ans q e w q' → Trans (q, some e) (some (.inr (.ans e w))) (q', none)

/-- The transition system of `L` from host state `q`. -/
def lts (q : L.S) : LTS Sig.empty E := ⟨L.S × Option E.Op, (q, none), L.Trans⟩

/-- **The strategy of a stateful environment** from host state `q`. -/
def strategy (q : L.S) : Strategy Sig.empty E := Strategy.ofLTS (L.lts q)

/-- Transitions of the divergence-observing transition system of `L`: as `Trans`, and a silent
self-loop on a question that `L` may leave unanswered. -/
inductive DTrans : L.S × Option E.Op → Option (Move Sig.empty E) → L.S × Option E.Op → Prop
  /-- Accept a question. -/
  | ask (q : L.S) (e : E.Op) : DTrans (q, none) (some (.inr (.ask e))) (q, some e)
  /-- Answer it as `L` may, moving to the new state. -/
  | ans {q q' : L.S} {e : E.Op} {w : E.Ar e} :
      L.Ans q e w q' → DTrans (q, some e) (some (.inr (.ans e w))) (q', none)
  /-- Diverge on a question that `L` may leave unanswered. -/
  | loop {q : L.S} {e : E.Op} : L.Silent q e → DTrans (q, some e) none (q, some e)

/-- The divergence-observing transition system of `L` from host state `q`. -/
def dlts (q : L.S) : LTS Sig.empty E := ⟨L.S × Option E.Op, (q, none), L.DTrans⟩

/-- **The divergence-observing strategy of a stateful environment** from host state `q`. -/
def dstrategy (q : L.S) : DStrategy Sig.empty E := DStrategy.ofLTS (L.dlts q)

/-- The stateless environment `K` as a one-state machine. -/
abbrev ofEnv (K : Env E) : SEnv E where
  S := Unit
  Ans _ e w _ := K.Answers e w
  Div _ _ := False

/-- The history machine of an environment strategy `τ`: the state is the list of events
so far, and a call may be answered with `w` when the extended history is a play of `τ`. -/
abbrev ofStrategy (τ : Strategy Sig.empty E) : SEnv E where
  S := List (Ev E)
  Ans u e w u' := u' = u ++ [.ask e, .ans e w] ∧ (u'.map Sum.inr : List (Move Sig.empty E)) ∈ τ
  Div _ _ := False

/-- Every answer of `L`, from every state, names an exception address below `n`. -/
def ThrowsBelow {ts : List FnType} (L : SEnv (ifaceSig ts)) (n : Nat) : Prop :=
  ∀ q e w q', L.Ans q e w q' → Answer.ThrowsBelow (ft := ts.get e.1) n w

/-- The stateless Core host of `L` in state `q`: a typed import call returns an answer of `L`
in state `q` without changing the store, or diverges when `L` may be silent. -/
def hostAt {ts : List FnType} (L : SEnv (ifaceSig ts)) (q : L.S) : HostSemantics Nat :=
  fun h s args out =>
    ∃ e, ifaceOp? ts h args = some e ∧
      ((∃ w q', L.Ans q e w q' ∧ out = .returned s (Answer.toResult (ft := ts.get e.1) w)) ∨
        (L.Silent q e ∧ out = .diverged))

end SEnv

/-- One step of Core reduction in product with the host state machine `L` (see the module
docstring). The host never changes the store. -/
inductive SStep {ts : List FnType} (P : Profile) (L : SEnv (ifaceSig ts)) :
    Config Nat × L.S → Config Nat × L.S → Prop where
  /-- A host-free Core step; the host state is unchanged. -/
  | internal {c c' : Config Nat} {q : L.S}
      (h : Execution.Core.Step P (fun _ _ _ _ => False) c c') : SStep P L (c, q) (c', q)
  /-- The host answers the import call `e` with `w`, moving from `q` to `q'`; the code
  continues with the Core result of the answer in the same store. -/
  | answer {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
      {w : (ifaceSig ts).Ar e} {q q' : L.S}
      (hd : decompose? c.store c.code = some (E, a, h, args))
      (op : ifaceOp? ts h args = some e) (ans : L.Ans q e w q') :
      SStep P L (c, q)
        (⟨c.store, c.frame, E.fill (Answer.toResult (ft := ts.get e.1) w).toAdmin⟩, q')
  /-- The host diverges on the import call `e`: a self-loop. -/
  | silent {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
      {q : L.S} (hd : decompose? c.store c.code = some (E, a, h, args))
      (op : ifaceOp? ts h args = some e) (hs : L.Silent q e) :
      SStep P L (c, q) (c, q)

/-- Runs of the product semantics. -/
abbrev SSteps {ts : List FnType} (P : Profile) (L : SEnv (ifaceSig ts)) :
    Config Nat × L.S → Config Nat × L.S → Prop :=
  Relation.ReflTransGen (SStep P L)

/-- The behaviours of the configuration `c` against the stateful host `L` in state `q`:
Core results of finite product runs, and `diverges` for infinite product runs. -/
def sbehavioursOf {ts : List FnType} (P : Profile) (L : SEnv (ifaceSig ts)) (q : L.S)
    (c : Config Nat) : Set (Behaviour Val) :=
  {b | ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      SSteps P L (c, q) (c', q') ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour} ∪
    {b | b = .diverges ∧ InfiniteTrace (SStep P L) (c, q)}

namespace ScalarInstance

variable (I : ScalarInstance)

/-- The closed program of the instance at store `s` against the stateful environment `L` in
host state `q`: `L.strategy q ≫ I.strategy P s`. -/
noncomputable def closedS (P : Profile) (s : Store Nat) (L : SEnv I.E) (q : L.S) :
    Strategy Sig.empty I.F :=
  (L.strategy q).comp (I.strategy P s)

/-- **The closed program against a stateful environment as a divergence-observing strategy**:
the composite of the environment's and the instance's divergence-observing strategies. -/
noncomputable def closedSD (P : Profile) (s : Store Nat) (L : SEnv I.E) (q : L.S) :
    DStrategy Sig.empty I.F :=
  (L.dstrategy q).comp (I.dstrategy P s)

end ScalarInstance

end Silmaril.Wasm.Game
