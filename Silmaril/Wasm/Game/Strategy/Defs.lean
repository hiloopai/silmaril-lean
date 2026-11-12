module

public import Silmaril.Wasm.Game.Machine.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Games.LTS.Defs

/-!
# The strategy of a scalar Core 3.0 instance

A Core 3.0 module instance with scalar function imports and exports denotes a
strategy `I.strategy P s : Strategy I.E I.F` of Silmaril's game category
(`Silmaril.Games`), from the import signature `I.E = ifaceSig I.imports` to the
export signature `I.F = ifaceSig I.exports`. It is read off silmaril-lean's
single-threaded machine (`Silmaril.Wasm.SingleThreaded`), as the strategy
`Strategy.ofLTS` of a transition system on *hidden states*.

## Instances

A `ScalarInstance` is the data of an instantiated module, independent of how it
was instantiated: the scalar import types, the scalar export types with the
function addresses implementing them, and a store. The host type is `Nat`: a
host function with code `.host i` *is* import `i`. `WellFormed s` states that
`s` is a well-typed store, that the export addresses have the declared types,
and that every host function of `s` is an import of the declared type.
`Silmaril.Wasm.Game.Instantiate` builds instances from `instantiateOnce?`. The structure
itself is in `Silmaril.Wasm.Game.Instance`, so that executable checkers need not import
the game semantics.

## Hidden states and transitions

* `idle s`: no export call is active; `s` is the store;
* `running f s t`: the export call `f` is active and the thread `t` has
  control (Proponent to move);
* `waiting f s t e`: the thread `t` is stopped at a callout, played as the
  import call `e` (Opponent to move).

The transitions (`Trans`) are labelled by moves of `I.E ↠ I.F`:

* `call`: an export question `f = ⟨j, args⟩` starts the pending invocation
  `$invoke(addr j, args)`;
* `ucall`: the thread runs host-free (`Reach P`) to a callout `h args`, played
  as the import question `importOp? h args`;
* `uret`: the environment's answer `v` resumes the thread with the Core result
  `v.toResult` (`resumeResult`, the spec's `$lift_result`);
* `oret`: the thread runs host-free to a result `r`, answering the export
  question with `Answer.ofResult? r`; the store persists.

There are no silent transitions: host-free runs are folded into the visible
ones. Divergence (an infinite host-free run) and stuck configurations give no
move: the pending question is never answered.

## Profiles

Everything is parametric in a silmaril numerics profile `P` (`$ND`, the
relaxed choices `$R_*`, the NaN policy and the grow policy), with host-free
runs `Reach P` of the relational machine `InternalP P`. For a
nondeterministic profile (the spec semantics `Profile.spec nd R`: NaN
payloads from result sets, relaxed alternatives, `memory.grow`/`table.grow`
failing at any time) a running state may have several `ucall`/`oret`
successors, and `I.strategy P s` is a nondeterministic Silmaril strategy: the
union of the plays of all branches. The whole store persists from
one export call to the next (including after a trap); the thread is dropped.
Silmaril strategies are sets of multi-question plays, so this persistence is part
of the strategy itself.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable (I : ScalarInstance)

/-- The import signature (the lower interface). -/
abbrev E : Sig.{0} := ifaceSig I.imports

/-- The export signature (the upper interface). -/
abbrev F : Sig.{0} := ifaceSig I.exports

/-- The function address of export `j`. -/
def addr (j : Fin I.exports.length) : Nat := I.addrs.getD j 0

/-- Well-formedness of the instance at store `s`: `s` is well-typed, every export address
has its declared type, and every host function of `s` is an import of the declared type. -/
structure WellFormed (s : Store Nat) : Prop where
  storeOk : StoreOk s
  addrs_length : I.addrs.length = I.exports.length
  export_type : ∀ j, ∃ fi : FuncInst Nat, s.funcs[I.addr j]? = some fi ∧
    Expand fi.type (I.exports.get j).toComp
  host_type : ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi →
    fi.code = .host h → ∃ hlt : h < I.imports.length, Expand fi.type (I.imports.get ⟨h, hlt⟩).toComp

/-- Well-formedness at the initial store. -/
def Ok : Prop := I.WellFormed I.store

/-- The import question of a callout `h args`: import `h` with typed arguments. -/
noncomputable def importOp? (h : Nat) (args : List Val) : Option I.E.Op :=
  ifaceOp? I.imports h args

/-- The thread of an export question `f = ⟨j, args⟩`: the pending invocation of `addr j`. -/
def initThread (f : I.F.Op) : Thread := .pending (I.addr f.1) f.2.1

/-! ## Hidden states and transitions -/

/-- Hidden states of the strategy (see the module docstring). -/
inductive HState where
  /-- No export call is active; the store persists. -/
  | idle (s : Store Nat)
  /-- The export call `f` is active and its thread has control. -/
  | running (f : I.F.Op) (s : Store Nat) (t : Thread)
  /-- The export call `f` waits for the answer to the import call `e`. -/
  | waiting (f : I.F.Op) (s : Store Nat) (t : Thread) (e : I.E.Op)

/-- One move of the instance or of its environment, with its effect on the hidden state. -/
inductive Trans (P : Profile) : I.HState → Move I.E I.F → I.HState → Prop where
  /-- An export question starts the pending invocation (Opponent). -/
  | call (s : Store Nat) (f : I.F.Op) :
      Trans P (.idle s) (.inr (.ask f)) (.running f s (I.initThread f))
  /-- A host-free run to a callout asks the import question (Proponent). -/
  | ucall {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {h : Nat} {args : List Val}
      {e : I.E.Op} (run : Reach P (s, t) (s', t')) (callout : CalloutAt s' t' h args)
      (op : I.importOp? h args = some e) :
      Trans P (.running f s t) (.inl (.ask e)) (.waiting f s' t' e)
  /-- The environment's answer resumes the thread (Opponent). -/
  | uret {f : I.F.Op} {s : Store Nat} {t : Thread} {e : I.E.Op} (v : I.E.Ar e) :
      Trans P (.waiting f s t e) (.inl (.ans e v))
        (.running f s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)))
  /-- A host-free run to a result answers the export question (Proponent); the store
  persists. -/
  | oret {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {r : Result}
      {v : I.F.Ar f} (run : Reach P (s, t) (s', t')) (final : ResultAt s' t' r)
      (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
      Trans P (.running f s t) (.inr (.ans f v)) (.idle s')

/-- The game position of a hidden state. -/
def HState.pos {I : ScalarInstance} : I.HState → Pos I.E I.F
  | .idle _ => .idle
  | .running f _ _ => .run f
  | .waiting f _ _ e => .wait f e

/-- Runs of the transition system along a play. -/
inductive Path (P : Profile) : I.HState → List (Move I.E I.F) → I.HState → Prop where
  /-- The empty run. -/
  | nil (q : I.HState) : Path P q [] q
  /-- One more transition in front. -/
  | cons {q q' q'' : I.HState} {m : Move I.E I.F} {p : List (Move I.E I.F)} :
      Trans I P q m q' → Path P q' p q'' → Path P q (m :: p) q''

/-- The plays from store `s`: any number of export activations, the store persisting
between them. -/
def plays (P : Profile) (s : Store Nat) : Set (List (Move I.E I.F)) :=
  {p | ∃ q, I.Path P (.idle s) p q}

/-- The transition system of the instance from store `s` (profile `P`): hidden states,
no silent steps. -/
def lts (P : Profile) (s : Store Nat) : LTS I.E I.F where
  State := I.HState
  init := .idle s
  step x l y := ∃ m, l = some m ∧ I.Trans P x m y

/-- **The strategy of the instance** from store `s` (profile `P`): the strategy of its
transition system. The store is hidden: it appears in no move. -/
noncomputable def strategy (P : Profile) (s : Store Nat) : Strategy I.E I.F :=
  Strategy.ofLTS (I.lts P s)

/-- The strategy of the instance at its initial store. -/
noncomputable def σ (P : Profile) : Strategy I.E I.F := I.strategy P I.store

/-- A complete run from the idle store `s` to the idle store `s'` along the play `c` (any
number of complete export activations). -/
def Activation (P : Profile) (s : Store Nat) (c : List (Move I.E I.F)) (s' : Store Nat) :
    Prop :=
  I.Path P (.idle s) c (.idle s')

/-- The stores reachable from `s` by finitely many complete activations. -/
def ReachableStore (P : Profile) (s s' : Store Nat) : Prop :=
  ∃ c, I.Activation P s c s'

/-- Every environment answer `throw a` in the play `p` names an exception address below
`n` (exception answers carry raw store addresses, see `Silmaril.Wasm.Game.Signature`). -/
def PlayThrowsBelow (n : Nat) (p : List (Move I.E I.F)) : Prop :=
  ∀ (e : I.E.Op) (v : I.E.Ar e), (.inl (.ans e v) : Move I.E I.F) ∈ p →
    Answer.ThrowsBelow n v

end ScalarInstance

end Silmaril.Wasm.Game
