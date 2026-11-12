module

public import Silmaril.Games.Answer.Defs
public import Silmaril.Games.Handler.Thms
import Silmaril.Proofs.Games.Answer.Basic

/-!
# Answering machines and handlers: theorems

**Trace characterisation of an LTS strategy composed with a handler.**

* `LTS.denotes_of_pos`: a transition system whose steps follow the legality automaton (through
  a map of its states to game positions) and which accepts every Opponent move the automaton
  allows denotes `Strategy.ofLTS` of itself: its traces are exactly the plays of its strategy.
* `Strategy.mem_ofLTS_comp_ofHandler`: for such a system `L`, the plays of
  `(ofLTS L).comp (ofHandler h)` are exactly the traces of the parallel composition of `L` with
  the reduction semantics of `h`; `Strategy.ofLTS_comp_ofHandler` states it as an equation of
  strategies.

**Answering machines** (`LTS.ofAns g init`, `Silmaril.Games.Answer.Defs`):

* `LTS.denotes_ofAns`: an answering machine denotes its strategy.
* **`Strategy.ofAns_comp_ofHandler`**: an answering machine below a handler `h` is the answering
  machine of `h.overAns g`, which runs each program of `h` against `g` from the current state.
  The state persists across questions, so this is not a handler identity.
* **`Strategy.ofHandler_comp_ofAns`**: a handler below an answering machine is irrelevant, since
  the machine makes no calls.
* `Prog.runAns_bind`, `Prog.runAns_interp`, `Handler.overAns_comp`: running programs against an
  answering machine commutes with sequencing and interpretation.

Proofs in `Silmaril.Proofs.Games.Answer.Basic`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F G H : Sig.{u}} {σ : Type u}

/-- **A transition system following the legality automaton denotes its strategy.** -/
theorem LTS.denotes_of_pos {L : LTS E F} (pos : L.State → Pos E F) (h₀ : pos L.init = .idle)
    (hs : ∀ {x l y}, L.step x l y → Path (pos x) l.toList (pos y))
    (hr : ∀ {x o p'}, Step (pos x) o p' → o.IsO → ∃ y, L.Run x [o] y) :
    L.Denotes (Strategy.ofLTS L) :=
  Silmaril.Proofs.Games.Answer.denotes_of_pos pos h₀ hs hr

/-- **Trace characterisation of an LTS strategy composed with a handler.** -/
theorem Strategy.mem_ofLTS_comp_ofHandler {L : LTS E F} (hL : L.Denotes (Strategy.ofLTS L))
    (h : Handler F G) {p : List (Move E G)} :
    p ∈ (Strategy.ofLTS L).comp (Strategy.ofHandler h) ↔
      p ∈ (L.comp h.toReduction.toLTS).Traces :=
  ((hL.comp (Handler.denotes_toLTS h)) p).symm

/-- An LTS strategy composed with a handler is the strategy of the parallel composition. -/
theorem Strategy.ofLTS_comp_ofHandler {L : LTS E F} (hL : L.Denotes (Strategy.ofLTS L))
    (h : Handler F G) :
    (Strategy.ofLTS L).comp (Strategy.ofHandler h) =
      Strategy.ofLTS (L.comp h.toReduction.toLTS) :=
  (hL.comp (Handler.denotes_toLTS h)).ofLTS_eq.symm

/-- An answering machine denotes its strategy. -/
theorem LTS.denotes_ofAns (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) :
    (LTS.ofAns g init : LTS E F).Denotes (Strategy.ofLTS (LTS.ofAns g init)) :=
  Silmaril.Proofs.Games.Answer.denotes_ofAns g init

/-- **An answering machine below a handler** is the answering machine of `h.overAns g`. -/
theorem Strategy.ofAns_comp_ofHandler (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ)
    (h : Handler F G) :
    (Strategy.ofLTS (LTS.ofAns g init : LTS E F)).comp (Strategy.ofHandler h) =
      Strategy.ofLTS (LTS.ofAns (h.overAns g) init) :=
  LTS.Denotes.eq_of_simulation ((LTS.denotes_ofAns g init).comp (Handler.denotes_toLTS h))
    (LTS.denotes_ofAns _ init) (Silmaril.Proofs.Games.Answer.ansSim g init h)
    (Silmaril.Proofs.Games.Answer.ansSim' g init h)

/-- **A handler below an answering machine is irrelevant.** -/
theorem Strategy.ofHandler_comp_ofAns (h : Handler E F) (g : (q : G.Op) → σ → G.Ar q × σ)
    (init : σ) :
    (Strategy.ofHandler h).comp (Strategy.ofLTS (LTS.ofAns g init : LTS F G)) =
      Strategy.ofLTS (LTS.ofAns g init : LTS E G) :=
  LTS.Denotes.eq_of_simulation ((Handler.denotes_toLTS h).comp (LTS.denotes_ofAns g init))
    (LTS.denotes_ofAns g init) (Silmaril.Proofs.Games.Answer.belowSim h g init)
    (Silmaril.Proofs.Games.Answer.belowSim' h g init)

/-- Running a sequenced program. -/
theorem Prog.runAns_bind {A B : Type u} (g : (q : F.Op) → σ → F.Ar q × σ) (P : Prog F A)
    (f : A → Prog F B) (s : σ) :
    (P.bind f).runAns g s = (f (P.runAns g s).1).runAns g (P.runAns g s).2 := by
  induction P generalizing s with
  | pure a => rfl
  | call m k ih => exact ih (g m s).1 (g m s).2

/-- Running an interpreted program: the handler runs against the machine. -/
theorem Prog.runAns_interp {A : Type u} (g : (q : F.Op) → σ → F.Ar q × σ) (h : Handler F G)
    (P : Prog G A) (s : σ) : (P.interp h).runAns g s = P.runAns (h.overAns g) s := by
  induction P generalizing s with
  | pure a => rfl
  | call m k ih =>
    show ((h m).bind fun n => (k n).interp h).runAns g s =
      (k ((h m).runAns g s).1).runAns (h.overAns g) ((h m).runAns g s).2
    rw [Prog.runAns_bind]
    exact ih _ _

/-- Composite handlers run layer by layer. -/
theorem Handler.overAns_comp (g : (q : F.Op) → σ → F.Ar q × σ) (h₁ : Handler F G)
    (h₂ : Handler G H) : (h₁.comp h₂).overAns g = h₂.overAns (h₁.overAns g) := by
  funext q s
  exact Prog.runAns_interp g h₁ (h₂ q) s

end Silmaril.Games
