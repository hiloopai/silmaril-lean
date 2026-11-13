module

public import Silmaril.Wasm.Game.StatefulEnv.Defs

/-!
# Games with the store in the moves: hosts that read and write the store

The game semantics of `Silmaril.Wasm.Game.{Strategy,StatefulEnv}` hides the
store inside the instance strategy, so an environment can only answer import
calls with values, traps or exception addresses: it never reads or writes the
module's memories, tables, globals or heap objects. Core 3.0's host interface
is more general: a host call `host h s vs (.returned s' r)` sees the whole store
`s` and returns a new store `s'` (`Step.callRefHost` continues in `s'`), subject
to the host contract `HostOk` (`StoreOk s'`, `Extend s s'`, a typed result).
This module gives the game for that interface.

## Design: the store travels with the moves

The **shared signature** `sharedSig ts` has as operations `⟨i, (s, args)⟩`: a
call of function `i` with typed arguments *in the store `s`*, and as answers
`(s', w)`: the new store and the answer. This is the store-passing (CompCertO
style) reading of a host call: a question carries the caller's state, an
answer the callee's. We use it on **both** interfaces of an instance:

* `I.shStrategy P : Strategy (sharedSig I.imports) (sharedSig I.exports)` (M1)
  answers an export question `⟨j, (s, args)⟩` by running `$invoke(addr j, args)`
  in `s`; at a callout it asks the import question in the *current* store and
  resumes in the store of the answer; it answers with the final store. There is
  no hidden store: between calls the instance is idle, and the next question
  brings its store.
* An environment is a stateful, nondeterministic host state machine
  `L : SEnv (sharedSig I.imports)` (the `SEnv` of `Silmaril.Wasm.Game.StatefulEnv`,
  over the shared signature): `L.Ans q ⟨i, (s, args)⟩ (s', w) q'` may change the
  store arbitrarily. The well-formedness condition `I.ShEnvOk s₀ L` is the host
  contract read on the game (`ShAnswerOk`: a well-formed store extending the old
  one, an existing exception), for questions at well-formed stores extending
  `s₀` that call an existing host function.

Why the whole store and not explicit load/store moves for the imported
memories and globals: (1) it is exactly Core's host interface, so every
`HostOk` host is an environment (`SEnv.ofHost`) with no new semantics; (2) it is
uniform: one signature covers memories, tables, globals, GC objects and
exceptions, which load/store moves would have to enumerate (and GC objects
have no fixed set of locations); (3) for composition and linking, both sides of
a link act on **one** store (silmaril-lean's linker produces a single store), so
a provider can be the environment of a consumer only if questions and answers
of the shared interface carry that store: store-passing on both interfaces makes
`I.shStrategy` composable as `σ_provider ≫ σ_consumer` in the category of
`Silmaril.Games`, with no splitting of the store. Encapsulation (an environment that
only touches imported or exported state) is a property of `L`, not of the game.

## Operations

`ShStep P L` is Core reduction in product with `L` (as `SStep` of
`Silmaril.Wasm.Game.StatefulEnv`), except that an answer `(s', w)` continues the
code in the store `s'`: exactly Core's `callRefHost` reduct. `shBehavioursOf`
are its behaviours (results of finite runs, `diverges` for infinite runs).

## Divergence

`I.shLts P` has the host-free machine steps as silent steps;
`I.shDStrategy P = DStrategy.ofLTS (I.shLts P)` observes divergence, and the
closed program `I.closedShD P L q = (L.dstrategy q).comp (I.shDStrategy P)` is a
composite in the divergence-observing category; `shDCompositeObs` reads Core
behaviours off it.

## The old games as special cases

* `SEnv.liftSh L`: a store-preserving stateful environment `L : SEnv (ifaceSig ts)`
  answers in the store of the question.
* `SEnv.ofHost ts host`: any Core host relation as a one-state environment.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- **The shared signature** of a scalar function interface: a call of function `i` with typed
arguments in a store, answered by a new store and an answer. -/
abbrev sharedSig (ts : List FnType) : Sig.{0} where
  Op := Σ i : Fin ts.length, Store Nat × Typed (ts.get i).params
  Ar e := Store Nat × Answer (ts.get e.1)

/-- The call `e` of the store-free interface, made in the store `s`. -/
def shOp {ts : List FnType} (s : Store Nat) (e : (ifaceSig ts).Op) : (sharedSig ts).Op :=
  ⟨e.1, (s, e.2)⟩

/-- The store-free call of a shared question. -/
def shCall {ts : List FnType} (e : (sharedSig ts).Op) : (ifaceSig ts).Op := ⟨e.1, e.2.2⟩

namespace ScalarInstance

variable (I : ScalarInstance)

/-- The shared import signature. -/
abbrev shE : Sig.{0} := sharedSig I.imports

/-- The shared export signature. -/
abbrev shF : Sig.{0} := sharedSig I.exports

/-- Every host function of `s` is an import of the declared type (the `host_type` part of
`WellFormed`). -/
def HostsTyped (s : Store Nat) : Prop :=
  ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi → fi.code = .host h →
    ∃ hlt : h < I.imports.length, Expand fi.type (I.imports.get ⟨h, hlt⟩).toComp

/-- A well-formed answer `(s', w)` to a question in the store `s`: the host contract of Core
(`HostOk`: a well-typed store extending `s`, a typed result; scalar values are typed in every
store, an exception must exist in `s'`), and the host functions of `s'` are imports. -/
structure ShAnswerOk (s : Store Nat) {ft : FnType} (s' : Store Nat) (w : Answer ft) : Prop where
  wf : I.WellFormed s'
  extend : Extend s s'
  throws : w.ThrowsBelow s'.exns.length

/-- **Well-formed environments over the shared signature**, from the store `s₀`: every answer
to a question at a well-formed store extending `s₀` that calls an existing host function is
well formed. -/
def ShEnvOk (s₀ : Store Nat) (L : SEnv I.shE) : Prop :=
  ∀ (q : L.S) (e : I.shE.Op) (a : I.shE.Ar e) (q' : L.S), Extend s₀ e.2.1 →
    I.WellFormed e.2.1 → (∃ fi ∈ e.2.1.funcs, fi.code = .host e.1.val) → L.Ans q e a q' →
    I.ShAnswerOk e.2.1 a.1 a.2

/-- A host relation keeps host functions typed as imports: the stores it returns from
well-formed stores have only import host functions. -/
def HostKeeps (host : HostSemantics Nat) : Prop :=
  ∀ (h : Nat) (s : Store Nat) (vs : List Val) (s' : Store Nat) (r : Result), I.WellFormed s →
    host h s vs (.returned s' r) → I.HostsTyped s'

/-- The thread of an export question `⟨j, (s, args)⟩`: the pending invocation of `addr j`. -/
def shInit (f : I.shF.Op) : Thread := .pending (I.addr f.1) f.2.2.1

/-- Hidden states of the store-passing strategy: no store while idle. -/
inductive ShState where
  /-- No export call is active. -/
  | idle
  /-- The export call `f` is active, its thread `t` running in the store `s`. -/
  | running (f : I.shF.Op) (s : Store Nat) (t : Thread)
  /-- The export call `f` waits for the answer to the import question `e`. -/
  | waiting (f : I.shF.Op) (s : Store Nat) (t : Thread) (e : I.shE.Op)

/-- The game position of a hidden state. -/
def ShState.pos {I : ScalarInstance} : I.ShState → Pos I.shE I.shF
  | .idle => .idle
  | .running f _ _ => .run f
  | .waiting f _ _ e => .wait f e

/-- Transitions of the store-passing instance, host-free steps silent. -/
inductive ShTrans (P : Profile) : I.ShState → Option (Move I.shE I.shF) → I.ShState → Prop where
  /-- An export question starts the invocation in the store it carries (Opponent). -/
  | call (f : I.shF.Op) : ShTrans P .idle (some (.inr (.ask f))) (.running f f.2.1 (I.shInit f))
  /-- A host-free machine step (silent). -/
  | tau {f : I.shF.Op} {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
      ShTrans P (.running f s t) none (.running f s' t')
  /-- A thread at a callout asks the import question in the current store (Proponent). -/
  | ucall {f : I.shF.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
      (callout : CalloutAt s t h args) (op : I.importOp? h args = some e) :
      ShTrans P (.running f s t) (some (.inl (.ask (shOp s e)))) (.waiting f s t (shOp s e))
  /-- The answer resumes the thread in the store of the answer (Opponent). -/
  | uret {f : I.shF.Op} {s : Store Nat} {t : Thread} {e : I.shE.Op} (s' : Store Nat)
      (v : Answer (I.imports.get e.1)) :
      ShTrans P (.waiting f s t e) (some (.inl (.ans e (s', v))))
        (.running f s' (resumeResult s t v.toResult))
  /-- A finished thread answers with its result and the final store (Proponent). -/
  | oret {f : I.shF.Op} {s : Store Nat} {t : Thread} {r : Result} {v : Answer (I.exports.get f.1)}
      (final : ResultAt s t r) (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
      ShTrans P (.running f s t) (some (.inr (.ans f (s, v)))) .idle

/-- The transition system of the store-passing instance. -/
def shLts (P : Profile) : LTS I.shE I.shF := ⟨I.ShState, .idle, I.ShTrans P⟩

/-- **The store-passing strategy of the instance** (M1). -/
noncomputable def shStrategy (P : Profile) : Strategy I.shE I.shF := Strategy.ofLTS (I.shLts P)

/-- **The divergence-observing store-passing strategy of the instance.** -/
noncomputable def shDStrategy (P : Profile) : DStrategy I.shE I.shF := DStrategy.ofLTS (I.shLts P)

/-- The closed program against the environment `L` in state `q`. -/
noncomputable def closedSh (P : Profile) (L : SEnv I.shE) (q : L.S) : Strategy Sig.empty I.shF :=
  (L.strategy q).comp (I.shStrategy P)

/-- **The closed program as a divergence-observing strategy**: a composite. -/
noncomputable def closedShD (P : Profile) (L : SEnv I.shE) (q : L.S) :
    DStrategy Sig.empty I.shF :=
  (L.dstrategy q).comp (I.shDStrategy P)

end ScalarInstance

/-- One step of Core reduction in product with an environment over the shared signature: a
host answer continues the code **in the store of the answer**. -/
inductive ShStep {ts : List FnType} (P : Profile) (L : SEnv (sharedSig ts)) :
    Config Nat × L.S → Config Nat × L.S → Prop where
  /-- A host-free Core step; the host state is unchanged. -/
  | internal {c c' : Config Nat} {q : L.S}
      (h : Execution.Core.Step P (fun _ _ _ _ => False) c c') : ShStep P L (c, q) (c', q)
  /-- The host answers the call `e` made in the current store with `(s', w)`. -/
  | answer {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
      {s' : Store Nat} {w : Answer (ts.get e.1)} {q q' : L.S}
      (hd : decompose? c.store c.code = some (E, a, h, args))
      (op : ifaceOp? ts h args = some e) (ans : L.Ans q (shOp c.store e) (s', w) q') :
      ShStep P L (c, q) (⟨s', c.frame, E.fill w.toResult.toAdmin⟩, q')
  /-- The host diverges on the call: a self-loop. -/
  | silent {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
      {q : L.S} (hd : decompose? c.store c.code = some (E, a, h, args))
      (op : ifaceOp? ts h args = some e) (hs : L.Silent q (shOp c.store e)) :
      ShStep P L (c, q) (c, q)

/-- Runs of the product semantics with the store-changing host. -/
abbrev ShSteps {ts : List FnType} (P : Profile) (L : SEnv (sharedSig ts)) :
    Config Nat × L.S → Config Nat × L.S → Prop :=
  Relation.ReflTransGen (ShStep P L)

/-- The behaviours of `c` against the store-changing host `L` in state `q`. -/
def shBehavioursOf {ts : List FnType} (P : Profile) (L : SEnv (sharedSig ts)) (q : L.S)
    (c : Config Nat) : Set (Behaviour Val) :=
  {b | ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      ShSteps P L (c, q) (c', q') ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour} ∪
    {b | b = .diverges ∧ InfiniteTrace (ShStep P L) (c, q)}

/-- The observations of a closed divergence-observing strategy over the shared signature for
the question `f`: the Core behaviours of its answers (any final store), and `diverges`. -/
def shDCompositeObs {ts : List FnType} (δ : DStrategy Sig.empty (sharedSig ts))
    (f : (sharedSig ts).Op) : Set (Behaviour Val) :=
  {b | ∃ (s' : Store Nat) (w : Answer (ts.get f.1)),
      Responds δ.toStrategy f (s', w) ∧ b = w.toBehaviour} ∪
    {b | b = .diverges ∧ [.inr (.ask f)] ∈ δ.div}

/-- The observations of a closed strategy over the shared signature for the question `f`: the
behaviours of its answers, and `diverges` when it never answers. -/
def shCompositeObs {ts : List FnType} (C : Strategy Sig.empty (sharedSig ts))
    (f : (sharedSig ts).Op) : Set (Behaviour Val) :=
  {b | ∃ (s' : Store Nat) (w : Answer (ts.get f.1)), Responds C f (s', w) ∧ b = w.toBehaviour} ∪
    {b | b = .diverges ∧ ∀ s' w, ¬ Responds C f (s', w)}

namespace SEnv

/-- **Every Core host relation is an environment over the shared signature**: a one-state
machine answering a call in store `s` as the host returns, and diverging when it may. -/
abbrev ofHost (ts : List FnType) (host : HostSemantics Nat) : SEnv (sharedSig ts) where
  S := Unit
  Ans _ e a _ := host e.1.val e.2.1 e.2.2.1 (.returned a.1 a.2.toResult)
  Div _ e := host e.1.val e.2.1 e.2.2.1 .diverged

/-- **A store-preserving environment over the shared signature**: `L` answers in the store of
the question. -/
abbrev liftSh {ts : List FnType} (L : SEnv (ifaceSig ts)) : SEnv (sharedSig ts) where
  S := L.S
  Ans q e a q' := a.1 = e.2.1 ∧ L.Ans q (shCall e) a.2 q'
  Div q e := L.Div q (shCall e)

end SEnv

end Silmaril.Wasm.Game
