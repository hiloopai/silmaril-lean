module

public import Silmaril.Games.Sig.Defs

/-!
# Moves and plays of the game `E ↠ F`

A component `E ↠ F` implements the operations of `F` and may call those of
`E` while doing so. Its game is the sequential, well-bracketed, alternating
game `!E ⊸ !F` of Koenig and Shao ("Refinement-Based Game Semantics for
Certified Abstraction Layers", LICS 2020) restricted to a single thread. There
are four kinds of moves:

| move | interface | player |
|---|---|---|
| `.inr (.ask q)` | question `q : F.Op` | Opponent (the environment calls us) |
| `.inl (.ask m)` | question `m : E.Op` | Proponent (we call below) |
| `.inl (.ans m n)` | answer `n : E.Ar m` | Opponent (the call returns) |
| `.inr (.ans q r)` | answer `r : F.Ar q` | Proponent (we return) |

A play is a list of moves, read from left to right. It is *legal* when it is
accepted by the four-state automaton `Step` from `Pos.idle`: the component is
idle, runs an `F`-question `q`, or waits for the answer to an `E`-question `m`
issued while running `q`. Answers carry the question they answer, and `Step`
checks that they match the pending question; this makes legality a
property of the list alone, with no justification pointers.

Plays are finite. Nothing distinguishes a component that has stopped forever
from one that is still computing: see `Silmaril.Games.Strategy.Defs` for the
consequences (divergence is not observable).
-/

@[expose] public section

namespace Silmaril.Games

universe u

/-- An event at one interface: a question, or an answer to a given question. -/
inductive Ev (E : Sig.{u}) : Type u
  /-- The question `m`. -/
  | ask (m : E.Op)
  /-- The answer `n` to the question `m`. -/
  | ans (m : E.Op) (n : E.Ar m)

/-- A move of the game `E ↠ F`: an event at the lower interface `E` (`inl`)
or at the upper interface `F` (`inr`). -/
abbrev Move (E F : Sig.{u}) : Type u := Ev E ⊕ Ev F

namespace Move

variable {E F : Sig.{u}}

/-- Opponent moves: upper questions and lower answers. -/
def IsO : Move E F → Prop
  | .inr (.ask _) => True
  | .inl (.ans _ _) => True
  | _ => False

/-- Proponent moves: lower questions and upper answers. -/
def IsP : Move E F → Prop
  | .inl (.ask _) => True
  | .inr (.ans _ _) => True
  | _ => False

end Move

/-- Positions of the game `E ↠ F`. -/
inductive Pos (E F : Sig.{u}) : Type u
  /-- No question is pending; Opponent may ask. -/
  | idle
  /-- The component is answering `q`; Proponent moves. -/
  | run (q : F.Op)
  /-- While answering `q` the component called `m`; Opponent answers `m`. -/
  | wait (q : F.Op) (m : E.Op)

/-- The legality automaton of `E ↠ F`. -/
inductive Step {E F : Sig.{u}} : Pos E F → Move E F → Pos E F → Prop
  /-- Opponent asks `q`. -/
  | ask (q : F.Op) : Step .idle (.inr (.ask q)) (.run q)
  /-- Proponent calls `m` while answering `q`. -/
  | call (q : F.Op) (m : E.Op) : Step (.run q) (.inl (.ask m)) (.wait q m)
  /-- Opponent answers the pending call `m`. -/
  | reply (q : F.Op) (m : E.Op) (n : E.Ar m) : Step (.wait q m) (.inl (.ans m n)) (.run q)
  /-- Proponent answers `q`. -/
  | ret (q : F.Op) (r : F.Ar q) : Step (.run q) (.inr (.ans q r)) .idle

/-- `Path x s y`: the automaton reads the moves `s` from `x` and ends in `y`. -/
inductive Path {E F : Sig.{u}} : Pos E F → List (Move E F) → Pos E F → Prop
  /-- The empty play. -/
  | nil (x : Pos E F) : Path x [] x
  /-- One more move in front. -/
  | cons {x y z : Pos E F} {o : Move E F} {s : List (Move E F)} :
      Step x o y → Path y s z → Path x (o :: s) z

/-- A legal play of `E ↠ F`: a list of moves accepted from the idle position. -/
def Legal {E F : Sig.{u}} (s : List (Move E F)) : Prop := ∃ y, Path .idle s y

/-! ## Projections and copycat plays -/

/-- The events of a play at the lower interface `E`. -/
def lower {E F : Sig.{u}} (s : List (Move E F)) : List (Ev E) := s.filterMap Sum.getLeft?

/-- The events of a play at the upper interface `F`. -/
def upper {E F : Sig.{u}} (s : List (Move E F)) : List (Ev F) := s.filterMap Sum.getRight?

namespace Ev

variable {E : Sig.{u}}

/-- A well-bracketed sequential exchange at one interface: questions and
their answers alternate, possibly ending with an unanswered question. -/
inductive Alternating : List (Ev E) → Prop
  /-- Nothing happened. -/
  | nil : Alternating []
  /-- A last question is pending. -/
  | ask (m : E.Op) : Alternating [.ask m]
  /-- A question, its answer, and more. -/
  | cons (m : E.Op) (n : E.Ar m) {w : List (Ev E)} :
      Alternating w → Alternating (.ask m :: .ans m n :: w)

/-- How the copycat strategy of `E ↠ E` forwards one event: a question arrives
on the right and is forwarded to the left; an answer arrives on the left and is
forwarded to the right. -/
def copy : Ev E → List (Move E E)
  | .ask m => [.inr (.ask m), .inl (.ask m)]
  | .ans m n => [.inl (.ans m n), .inr (.ans m n)]

/-- The copycat play forwarding the events `w`. -/
def double (w : List (Ev E)) : List (Move E E) := w.flatMap copy

end Ev

end Silmaril.Games
