module

public import Silmaril.Wasm.Game.Env.Defs
public import Silmaril.Games.DivLTS.Defs

/-!
# Divergence-observing strategies of instances and of closed programs

Under a nondeterministic profile a Core call may both answer (on one branch)
and diverge (on another). A plain Silmaril `Strategy` is a set of finite plays
and cannot record this, so adequacy of `I.strategy P s` keeps may-divergence
as the Core predicate `Diverges` (`Silmaril.Wasm.Game.Adequacy`). This module
gives the game-level reading, with the divergence-observing strategies of
`Silmaril.Games.DivLTS`:

* `I.dlts P s`: the transition system of the instance with the host-free
  machine steps (`InternalP P`) as **silent** steps, instead of folding them
  into the visible moves as `I.lts P s` does. Its divergence-observing
  strategy is `I.dstrategy P s = DStrategy.ofLTS (I.dlts P s)`: it may diverge
  after a play exactly when some run reading the play reaches a thread with an
  infinite host-free run.
* `K.dlts`: the environment, which *diverges* (a silent self-loop) on a
  question it never answers, matching the host relation `hostOf`, whose
  `.diverged` outcome is a Core self-loop (`Step.callRefHostDiv`).
* `I.closedD P s K = DStrategy.ofLTS (K.dlts.comp (I.dlts P s))`: the closed
  program as a divergence-observing strategy, the parallel composition of the
  two systems with the shared interface hidden (`LTS.comp`). Its finite plays
  are those of `K.strategy ≫ I.strategy P s` (`forget_closedD`); its
  divergences are the infinite silent runs of the composite system, which
  include infinite hidden chatter (infinitely many answered import calls), a
  call that `K` never answers, and an infinite host-free run.
* `dcompositeObs δ f`: the observations of a closed divergence-observing
  strategy for the question `f`: the behaviours of its answers, and
  `diverges` when it may diverge right after `[ask f]`.

Relation to `DStrategy.comp`: `I.closedD` is the strategy of the composite
*system*; `Silmaril.Wasm.Game.DivAdequacy.Thms` shows that it equals the composite
`K.dstrategy.comp (I.dstrategy P s)` of the two divergence-observing strategies
(`Silmaril.Games.DivComp`), through `DStrategy.ofLTS_comp`
(`Silmaril.Games.DivLTSComp`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

namespace Env

variable {E : Sig.{0}}

/-- Transitions of the divergence-observing transition system of an environment: as
`Env.Step`, and a silent self-loop on a question that is never answered. -/
inductive DStep (K : Env E) : Option E.Op → Option (Move Sig.empty E) → Option E.Op → Prop
  /-- Accept a question. -/
  | ask (e : E.Op) : DStep K none (some (.inr (.ask e))) (some e)
  /-- Answer it as `K` does. -/
  | ans {e : E.Op} {w : E.Ar e} : K.Answers e w → DStep K (some e) (some (.inr (.ans e w))) none
  /-- Diverge on a question that `K` never answers. -/
  | loop {e : E.Op} : (∀ w, ¬ K.Answers e w) → DStep K (some e) none (some e)

/-- The divergence-observing transition system of an environment. -/
def dlts (K : Env E) : LTS Sig.empty E := ⟨Option E.Op, none, K.DStep⟩

/-- The divergence-observing strategy of an environment. -/
def dstrategy (K : Env E) : DStrategy Sig.empty E := DStrategy.ofLTS K.dlts

end Env

namespace ScalarInstance

variable (I : ScalarInstance)

/-- Transitions of the instance with silent host-free steps. -/
inductive DTrans (P : Profile) : I.HState → Option (Move I.E I.F) → I.HState → Prop where
  /-- An export question starts the pending invocation (Opponent). -/
  | call (s : Store Nat) (f : I.F.Op) :
      DTrans P (.idle s) (some (.inr (.ask f))) (.running f s (I.initThread f))
  /-- A host-free machine step (silent). -/
  | tau {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
      DTrans P (.running f s t) none (.running f s' t')
  /-- A thread at a callout asks the import question (Proponent). -/
  | ucall {f : I.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
      (callout : CalloutAt s t h args) (op : I.importOp? h args = some e) :
      DTrans P (.running f s t) (some (.inl (.ask e))) (.waiting f s t e)
  /-- The environment's answer resumes the thread (Opponent). -/
  | uret {f : I.F.Op} {s : Store Nat} {t : Thread} {e : I.E.Op} (v : I.E.Ar e) :
      DTrans P (.waiting f s t e) (some (.inl (.ans e v)))
        (.running f s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)))
  /-- A finished thread answers the export question (Proponent); the store persists. -/
  | oret {f : I.F.Op} {s : Store Nat} {t : Thread} {r : Result} {v : I.F.Ar f}
      (final : ResultAt s t r) (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
      DTrans P (.running f s t) (some (.inr (.ans f v))) (.idle s)

/-- The transition system of the instance from store `s` with silent host-free steps. -/
def dlts (P : Profile) (s : Store Nat) : LTS I.E I.F := ⟨I.HState, .idle s, I.DTrans P⟩

/-- **The divergence-observing strategy of the instance** from store `s`. -/
noncomputable def dstrategy (P : Profile) (s : Store Nat) : DStrategy I.E I.F :=
  DStrategy.ofLTS (I.dlts P s)

/-- **The closed program as a divergence-observing strategy**: the composite of the
environment's and the instance's transition systems, the import interface hidden. -/
noncomputable def closedD (P : Profile) (s : Store Nat) (K : Env I.E) :
    DStrategy Sig.empty I.F :=
  DStrategy.ofLTS (K.dlts.comp (I.dlts P s))

end ScalarInstance

/-- The observations of a closed divergence-observing strategy `δ` for the question `f`: the
Core behaviours of its answers, and `diverges` when it may diverge right after `[ask f]`. -/
def dcompositeObs {ts : List FnType} (δ : DStrategy Sig.empty (ifaceSig ts))
    (f : (ifaceSig ts).Op) : Set (Silmaril.Wasm.Behaviour Val) :=
  {b | ∃ w, Responds δ.toStrategy f w ∧ b = Answer.toBehaviour (ft := ts.get f.1) w} ∪
    {b | b = .diverges ∧ [.inr (.ask f)] ∈ δ.div}

end Silmaril.Wasm.Game
