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

/-! ## Basic facts

The legality automaton is deterministic (`Step.det`, `Path.det`); paths split
along concatenation (`Path.append_iff`), so legal plays are closed under
prefixes (`Legal.of_prefix`). The game alternates: after an Opponent move only
Proponent may move and conversely (`Step.isP_of_isO`, `Step.isO_of_isP`).

They are stated here, with the definitions, because the strategy definitions
(`Silmaril.Games.Strategy.Defs`) need them in their proof fields;
`Silmaril.Games.Play.Thms` re-exports them.
-/

section Basic

variable {E F : Sig.{u}}

/-- No move belongs to both players. -/
theorem Move.not_isO_of_isP {o : Move E F} (h : o.IsP) : ¬ o.IsO := by
  rcases o with (_ | _) | (_ | _) <;> simp_all [Move.IsO, Move.IsP]

namespace Step

/-- The automaton is deterministic. -/
theorem det {x y z : Pos E F} {o : Move E F} (h₁ : Step x o y) (h₂ : Step x o z) : y = z := by
  cases h₁ <;> cases h₂ <;> rfl

/-- Every step is by exactly one of the players. -/
theorem isO_or_isP {x y : Pos E F} {o : Move E F} (h : Step x o y) : o.IsO ∨ o.IsP := by
  cases h <;> simp [Move.IsO, Move.IsP]

/-- Opponent moves exactly from the positions `idle` and `wait`. -/
theorem isO_iff {x y : Pos E F} {o : Move E F} (h : Step x o y) :
    o.IsO ↔ (x = .idle ∨ ∃ q m, x = .wait q m) := by
  cases h <;> simp [Move.IsO]

/-- After an Opponent move, Proponent moves. -/
theorem isP_of_isO {x y z : Pos E F} {o o' : Move E F} (h : Step x o y) (ho : o.IsO)
    (h' : Step y o' z) : o'.IsP := by
  cases h <;> cases h' <;> simp_all [Move.IsO, Move.IsP]

/-- After a Proponent move, Opponent moves. -/
theorem isO_of_isP {x y z : Pos E F} {o o' : Move E F} (h : Step x o y) (ho : o.IsP)
    (h' : Step y o' z) : o'.IsO := by
  cases h <;> cases h' <;> simp_all [Move.IsO, Move.IsP]

end Step

namespace Path

/-- Paths are deterministic. -/
theorem det {x y z : Pos E F} {s : List (Move E F)} (h₁ : Path x s y) (h₂ : Path x s z) :
    y = z := by
  induction h₁ generalizing z with
  | nil => cases h₂; rfl
  | cons hs _ ih =>
    cases h₂ with
    | cons hs' hp' => exact ih ((hs.det hs') ▸ hp')

/-- Paths compose along concatenation. -/
theorem append {x y z : Pos E F} {s t : List (Move E F)} (h₁ : Path x s y) (h₂ : Path y t z) :
    Path x (s ++ t) z := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

/-- A path through `s ++ t` passes through some intermediate position. -/
theorem of_append {x z : Pos E F} {s t : List (Move E F)} (h : Path x (s ++ t) z) :
    ∃ y, Path x s y ∧ Path y t z := by
  induction s generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o s ih =>
    cases h with
    | cons hs hp =>
      obtain ⟨y, h₁, h₂⟩ := ih hp
      exact ⟨y, .cons hs h₁, h₂⟩

/-- Paths split along concatenation. -/
theorem append_iff {x z : Pos E F} {s t : List (Move E F)} :
    Path x (s ++ t) z ↔ ∃ y, Path x s y ∧ Path y t z :=
  ⟨of_append, fun ⟨_, h₁, h₂⟩ => h₁.append h₂⟩

/-- A path through `s ++ [o]`. -/
theorem concat_iff {x z : Pos E F} {s : List (Move E F)} {o : Move E F} :
    Path x (s ++ [o]) z ↔ ∃ y, Path x s y ∧ Step y o z := by
  rw [append_iff]
  constructor
  · rintro ⟨y, h₁, h₂⟩
    cases h₂ with
    | cons hs hp => cases hp; exact ⟨y, h₁, hs⟩
  · rintro ⟨y, h₁, h₂⟩
    exact ⟨y, h₁, .cons h₂ (.nil _)⟩

/-- A one-move path is a step. -/
theorem single {x y : Pos E F} {o : Move E F} (h : Step x o y) : Path x [o] y := .cons h (.nil _)

end Path

namespace Legal

/-- The empty play is legal. -/
theorem nil : Legal ([] : List (Move E F)) := ⟨_, .nil _⟩

/-- Prefixes of legal plays are legal. -/
theorem of_prefix {s t : List (Move E F)} (ht : Legal t) (h : s <+: t) : Legal s := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨y, hy⟩ := ht
  obtain ⟨z, hz, -⟩ := Path.of_append hy
  exact ⟨z, hz⟩

end Legal

end Basic

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

/-- Copycat forwarding nothing. -/
@[simp] theorem double_nil : double ([] : List (Ev E)) = [] := rfl

/-- Copycat forwards events one at a time. -/
@[simp] theorem double_cons (x : Ev E) (w : List (Ev E)) :
    double (x :: w) = copy x ++ double w := by
  simp [double]

/-- Forwarding a question. -/
@[simp] theorem copy_ask (m : E.Op) : copy (.ask m) = [.inr (.ask m), .inl (.ask m)] := rfl

/-- Forwarding an answer. -/
@[simp] theorem copy_ans (m : E.Op) (n : E.Ar m) :
    copy (.ans m n) = [.inl (.ans m n), .inr (.ans m n)] := rfl

end Ev

end Silmaril.Games
