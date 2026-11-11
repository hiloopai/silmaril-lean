module

public import Silmaril.Games.Play.Defs

/-!
# Plays: basic facts

The legality automaton is deterministic (`Step.det`, `Path.det`); paths split
along concatenation (`Path.append_iff`), so legal plays are closed under
prefixes (`Legal.of_prefix`). The game alternates: after an Opponent move only
Proponent may move and conversely (`Step.isP_of_isO`, `Step.isO_of_isP`).
-/

@[expose] public section

namespace Silmaril.Games

universe u

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

end Silmaril.Games

namespace Silmaril.Games.Ev

universe u

variable {E : Sig.{u}}

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

end Silmaril.Games.Ev
