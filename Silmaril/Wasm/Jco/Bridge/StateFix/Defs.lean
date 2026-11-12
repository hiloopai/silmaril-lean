module

public import Silmaril.Wasm.Jco.Bridge.State.Defs

/-!
# The stateful component bridge, restated

`SimpleCompState` (`Silmaril.Wasm.Jco.Bridge.State`) says that the IR strategy of
`Fuse.simpleComp` over a stateful module is the machine `compLTS`, which answers by `compAns`.
`compAns` is `stateCall` and **keeps the old state whenever `stateCall` fails**. One failure
comes *after* the module has run: the call returns, its flat results do not lift at the
world's result type (`liftRes` is `none`), and the component traps. In the IR the core
instance has then already moved to its new state (`SMod.Step.ret` takes `(m.ans q s).2`), and a
`canon lift` trap does not roll it back. So `compAns` and the IR disagree on such modules from
the next call on.

This module states the corrected target and the pieces used to compare the two:

* `AnsStep f`, `ansLTS f init`: the machine over `sigU` that answers each question by
  `f q s` in its state `s` (`compLTS md m` is `ansLTS (compAns md m) m.init`, proved in
  `Thms`).
* **`compAnsS md m`**: the component's answer with the state the IR keeps. Lowering failures and
  traps of the module keep the state; a call that returns moves to the module's new state, also
  when its results do not lift.
* **`SimpleCompStateS`** (open, a frozen `Prop`): the IR strategy of `Fuse.simpleComp`
  over a stateful module is `ansLTS (compAnsS md m) m.init`.
* `LiftTotal md m`: every returned call of a world function lifts. On such modules `compAnsS`
  is `compAns`.
* `bumpMeta`, `bumpMod`: a world function `f : () -> u32` over a module with state `Bool` whose
  first call returns no value (a lift failure) and moves to `true`, after which it returns
  `7`. Here the two machines differ.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco (PTy PVal Sig Meta)

variable {σ : Type}

/-- The steps of a machine over `sigU` that answers question `q` in state `s` by `f q s`. -/
inductive AnsStep (f : sigU.Op → σ → Option Payload × σ) :
    σ × Option sigU.Op → Option (Move sigU sigU) → σ × Option sigU.Op → Prop
  | ask (s : σ) (q : sigU.Op) : AnsStep f (s, none) (some (.inr (.ask q))) (s, some q)
  | ret (s : σ) (q : sigU.Op) :
      AnsStep f (s, some q) (some (.inr (.ans q (f q s).1))) ((f q s).2, none)

/-- The answering machine of `f` from state `init`. -/
def ansLTS (f : sigU.Op → σ → Option Payload × σ) (init : σ) : LTS sigU sigU :=
  ⟨σ × Option sigU.Op, (init, none), AnsStep f⟩

/-- The answers to a sequence of questions from state `s`, and the final state. -/
def ansList (f : sigU.Op → σ → Option Payload × σ) : σ → List sigU.Op → List (Option Payload) × σ
  | s, [] => ([], s)
  | s, q :: qs =>
    let p := f q s
    let r := ansList f p.2 qs
    (p.1 :: r.1, r.2)

/-- The play of the questions `qs` answered by `rs`, one question at a time. -/
def ansPlays : List sigU.Op → List (Option Payload) → List (Move sigU sigU)
  | q :: qs, r :: rs => .inr (.ask q) :: .inr (.ans q r) :: ansPlays qs rs
  | _, _ => []

/-- **The component's answer with the state the IR keeps**: a returned call of the module moves
to its new state even when its results do not lift. -/
def compAnsS (md : Meta) (m : SMod σ) : sigU.Op → σ → Option Payload × σ
  | (i, .vals vs), st =>
    match md.world[i]? with
    | some s =>
      match checkLower (s.params.map PTy.toVal) vs with
      | some xs =>
        match m.callN s.name xs st with
        | some (ys, st') => ((liftRes s.result ys).map resPayload, st')
        | none => (none, st)
      | none => (none, st)
    | none => (none, st)
  | (_, .flat _), st => (none, st)

/-- The corrected component machine. -/
def compLTSS (md : Meta) (m : SMod σ) : LTS sigU sigU := ansLTS (compAnsS md m) m.init

/-- **Statement, restated and proved** (`simpleComp_stateS` in `Silmaril.Wasm.Jco.Bridge.StateProof.Thms`): the IR strategy of the adaptor-style component of the simple FFI
style over a stateful module is the machine answering by `compAnsS`, on memory-free worlds. -/
def SimpleCompStateS : Prop :=
  ∀ (σ : Type) (md : Meta) (m : SMod σ), md.memFree = true →
    (Silmaril.Wasm.Jco.Fuse.simpleComp [] (Meta.iface md) m).denU
        (Silmaril.Wasm.Jco.Fuse.baseSem (smodSem σ)) = Strategy.ofLTS (compLTSS md m)

/-- Every returned call of a world function lifts at its result type. -/
def LiftTotal (md : Meta) (m : SMod σ) : Prop :=
  ∀ s ∈ md.world, ∀ xs st ys st', m.callN s.name xs st = some (ys, st') →
    (liftRes s.result ys).isSome

/-! ## The counterexample -/

/-- One world function `f : () -> u32`. -/
def bumpMeta : Meta := ⟨[⟨"f", [], some (.val .u32)⟩], "alloc"⟩

/-- Silmaril.Wasm.Component.Export `f` returns no value in state `false` (its result does not lift) and moves to `true`;
in state `true` it returns `7`. -/
def bumpMod : SMod Bool where
  exports := [("f", ⟨[], [.int .i32]⟩)]
  init := false
  fn _ _ b := if b then some ([Flat.i32 7], true) else some ([], true)

/-- The question: call world function `0` with no arguments. -/
def bumpQ : sigU.Op := (0, .vals [])

end Silmaril.Wasm.Jco.Bridge
