module

public import Silmaril.Wasm.Jco.Bridge.Defs
public import Silmaril.Games.LTS.Defs

/-!
# Relating the two settings beyond pure modules: stateful modules

`Silmaril.Wasm.Jco.Bridge` relates the memory-based model and the component IR on **pure** modules
(`PMod`, stateless exports). This module adds **stateful** modules: core modules without imports
or memory whose exports are deterministic functions of their flat arguments **and an
instance state** (`SMod σ`, with state type `σ` and initial state `init`). Such a module is

* a core instance of the memory-based model, `SMod.inst m`: state `σ`, an empty memory, and
  `call n` the state-passing function `fn n` (`RM.ofFun`);
* a core module of the IR, with the semantics `smodSem σ`: the strategy of the state machine
  `SMod.lts m`. Between questions the machine holds the instance state. On a question it
  answers by `SMod.ans` and moves to the new state. A trap (answer `none`) leaves the state
  unchanged.

## The common state-passing function

On the memory-free fragment both settings compute with `stateCall m s vs st`: type check and
lower the arguments, call the export named `s.name` in state `st`, lift the result. It returns
the result and the new state, or `none` for a trap. `specState md m` is the memory-based
behaviour it gives, `RM.ofFun` of `stateCall`.

## The open target

`compAns md m` answers the component's questions by `stateCall`, and `compLTS md m` is the state
machine over `sigU` that answers with it. **`SimpleCompState`** (open, a frozen `Prop`) is
the statement that the IR strategy of the adaptor-style component `Fuse.simpleComp` over a
stateful module is the strategy of `compLTS`. For pure modules this is
`Bridge.simpleComp_bridge`, which is proved with handlers. A stateful module's strategy is not a
handler, so that proof does not carry over. What is proved here is stated in
`Silmaril.Wasm.Jco.Bridge.State.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

/-- The deterministic computation of a state-passing function (`none`: a trap). -/
def RM.ofFun {σ α : Type} (f : σ → Option (α × σ)) : RM σ α := fun s o =>
  match f s with
  | some (a, s') => o = .ok a s'
  | none => o = .trap

end Silmaril.Wasm.Jco

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco (PTy PVal Sig Meta)

/-! ## Stateful modules -/

/-- A stateful core module: no imports, deterministic exports over an instance state. -/
structure SMod (σ : Type) where
  exports : CoreIface
  init : σ
  fn : String → List Flat → σ → Option (List Flat × σ)

variable {σ : Type}

instance : CoreModule (SMod σ) where
  imports _ := []
  exports := SMod.exports

namespace SMod

/-- Calling the export named `n` in state `s` (a trap if there is none). -/
def callN (m : SMod σ) (n : String) (xs : List Flat) (s : σ) : Option (List Flat × σ) :=
  if m.exports.any (·.1 == n) then m.fn n xs s else none

/-- **The memory-based instance** of a stateful module. -/
def inst (m : SMod σ) : Silmaril.Wasm.Jco.CoreInst where
  St := σ
  mem _ := []
  setMem s _ := s
  call n xs := Silmaril.Wasm.Jco.RM.ofFun (m.callN n xs)

/-- The questions of the IR interface of `m`. -/
abbrev Q (m : SMod σ) : Type := (CoreIface.sig m.exports).Op

/-- **The answer of the module** to a question in state `s`, and the next state. -/
def ans (m : SMod σ) (q : m.Q) (s : σ) : Option Payload × σ :=
  match q.2 with
  | .flat xs =>
    match m.fn (m.exports[q.1]).1 xs s with
    | some (ys, s') => (some (.flat ys), s')
    | none => (none, s)
  | .vals _ => (none, s)

/-- The moves of the IR game of `m`. -/
abbrev Mv (m : SMod σ) : Type := Move (CoreIface.sig []) (CoreIface.sig m.exports)

/-- The steps of the state machine of `m`: accept a question, then answer it. -/
inductive Step (m : SMod σ) : σ × Option m.Q → Option m.Mv → σ × Option m.Q → Prop
  | ask (s : σ) (q : m.Q) : Step m (s, none) (some (.inr (.ask q))) (s, some q)
  | ret (s : σ) (q : m.Q) :
      Step m (s, some q) (some (.inr (.ans q (m.ans q s).1))) ((m.ans q s).2, none)

/-- **The state machine of `m`.** -/
def lts (m : SMod σ) : LTS (CoreIface.sig []) (CoreIface.sig m.exports) :=
  ⟨σ × Option m.Q, (m.init, none), Step m⟩

/-- The answers to a sequence of questions from state `s`, and the final state. -/
def answers (m : SMod σ) : σ → List m.Q → List (Option Payload) × σ
  | s, [] => ([], s)
  | s, q :: qs =>
    let p := m.ans q s
    let r := answers m p.2 qs
    (p.1 :: r.1, r.2)

/-- The play of the questions `qs` answered by `rs`, one question at a time. -/
def plays (m : SMod σ) : List m.Q → List (Option Payload) → List m.Mv
  | q :: qs, r :: rs => .inr (.ask q) :: .inr (.ans q r) :: plays m qs rs
  | _, _ => []

end SMod

/-- A pure module as a stateful module with one state. -/
def PMod.toS (m : PMod) : SMod Unit := ⟨m.exports, (), fun n xs _ => (m.fn n xs).map (·, ())⟩

/-- **The IR semantics of stateful modules**: each module is its state machine. -/
def smodSem (σ : Type) : CoreSem (SMod σ) := ⟨fun m => Strategy.ofLTS m.lts⟩

/-! ## The common state-passing function -/

/-- **A call of a world function of a stateful module**, on the memory-free fragment. -/
def stateCall (m : SMod σ) (s : Sig) (vs : List Val) (st : σ) : Option (Option PVal × σ) :=
  (checkLower (s.params.map PTy.toVal) vs).bind fun xs =>
    (m.callN s.name xs st).bind fun p => (liftRes s.result p.1).map fun r => (r, p.2)

/-- **The memory-based answers**: export `name` is `stateCall` of the first world function named
`name`. -/
def specState (md : Meta) (m : SMod σ) (name : String) (vs : List Val) :
    Silmaril.Wasm.Jco.RM σ (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some s => Silmaril.Wasm.Jco.RM.ofFun (stateCall m s vs)
  | none => Silmaril.Wasm.Jco.RM.fail

/-! ## The open component-level target -/

/-- The component's answer to a question in state `st`: `stateCall` of world function `i` on
component values. Anything else traps and leaves the state. -/
def compAns (md : Meta) (m : SMod σ) : sigU.Op → σ → Option Payload × σ
  | (i, .vals vs), st =>
    match md.world[i]? with
    | some s =>
      match stateCall m s vs st with
      | some (r, st') => (some (resPayload r), st')
      | none => (none, st)
    | none => (none, st)
  | (_, .flat _), st => (none, st)

/-- The steps of the component's state machine. -/
inductive CompStep (md : Meta) (m : SMod σ) :
    σ × Option sigU.Op → Option (Move sigU sigU) → σ × Option sigU.Op → Prop
  | ask (s : σ) (q : sigU.Op) : CompStep md m (s, none) (some (.inr (.ask q))) (s, some q)
  | ret (s : σ) (q : sigU.Op) :
      CompStep md m (s, some q) (some (.inr (.ans q (compAns md m q s).1)))
        ((compAns md m q s).2, none)

/-- The component's state machine, from the module's initial state. -/
def compLTS (md : Meta) (m : SMod σ) : LTS sigU sigU := ⟨σ × Option sigU.Op, (m.init, none), CompStep md m⟩

/-- **Statement, refuted** (`not_simpleComp_state` in `Silmaril.Wasm.Jco.Bridge.StateProof.Thms`; the corrected form is `SimpleCompStateS`): the IR strategy of the adaptor-style component of the simple FFI style over
a stateful module is the strategy of its state machine `compLTS`, on memory-free worlds. -/
def SimpleCompState : Prop :=
  ∀ (σ : Type) (md : Meta) (m : SMod σ), md.memFree = true →
    (Silmaril.Wasm.Jco.Fuse.simpleComp [] (Meta.iface md) m).denU
        (Silmaril.Wasm.Jco.Fuse.baseSem (smodSem σ)) = Strategy.ofLTS (compLTS md m)

end Silmaril.Wasm.Jco.Bridge
