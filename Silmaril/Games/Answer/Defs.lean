module

public import Silmaril.Games.Handler.Defs

/-!
# Answering machines

A stateful component that makes no calls and answers each question at once:

* `LTS.AnsStep g`, `LTS.ofAns g init`: the transition system with state `σ` that, between
  questions, holds a state `s`; on a question `q` it answers `(g q s).1` and moves to
  `(g q s).2`. It has no silent steps and no moves on its lower interface, so any `E` can be
  put below it.
* `Prog.runAns g P s`: run a program over `F` against such a machine from state `s`, answering
  each call by `g`; it returns the program's result and the final state.

`Silmaril.Games.Answer.Thms` shows that the strategy of an answering machine below a handler is
the answering machine of `fun q s => (h q).runAns g s` (`Strategy.ofAns_comp_ofHandler`), and
that a handler below an answering machine is irrelevant (`Strategy.ofHandler_comp_ofAns`).
-/

@[expose] public section

namespace Silmaril.Games

universe u

variable {E F G : Sig.{u}} {σ : Type u}

namespace LTS

/-- The steps of the answering machine of `g`: accept a question, then answer it. -/
inductive AnsStep (g : (q : F.Op) → σ → F.Ar q × σ) :
    σ × Option F.Op → Option (Move E F) → σ × Option F.Op → Prop
  /-- Accept the question `q` in state `s`. -/
  | ask (s : σ) (q : F.Op) : AnsStep g (s, none) (some (.inr (.ask q))) (s, some q)
  /-- Answer `q` in state `s`. -/
  | ret (s : σ) (q : F.Op) :
      AnsStep g (s, some q) (some (.inr (.ans q (g q s).1))) ((g q s).2, none)

/-- **The answering machine** of `g` from state `init`. -/
def ofAns (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) : LTS E F :=
  ⟨σ × Option F.Op, (init, none), AnsStep g⟩

end LTS

/-- Run a program against an answering machine from state `s`. -/
def Prog.runAns {A : Type u} (g : (q : F.Op) → σ → F.Ar q × σ) : Prog F A → σ → A × σ
  | .pure a, s => (a, s)
  | .call m k, s => (k (g m s).1).runAns g (g m s).2

/-- The answers of a handler `h` over the answering machine of `g`. -/
def Handler.overAns (g : (q : F.Op) → σ → F.Ar q × σ) (h : Handler F G) :
    (q : G.Op) → σ → G.Ar q × σ :=
  fun q s => (h q).runAns g s

end Silmaril.Games
