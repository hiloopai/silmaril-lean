module

public import Silmaril.Games.Abstract.Hiding.Defs

/-!
# Exported state: cells next to a game

A module that exports memories, globals or tables lets its environment read
and write that state directly, not only through function calls.
`G.withCells N V` adds named cells `n : N` with values `V n` to a game `G`:

* `op m`: a move of `G` (function calls and answers);
* `get n` (environment) asks for the value of cell `n`, and the component
  answers at once with `got n v`;
* `set n v` (environment) writes `v` into cell `n`.

A play is legal when its `G`-moves form a legal play of `G` and every `get` is
answered at once by a `got` of the same cell. How the cells behave is a
property of the model, not of the game: a write visible through another name
(aliasing, for example two exports of one memory), a function that mutates a
cell, a cell no function reads. Each is a set of plays.

* `Game.Hom.ops`: the function-only game embeds (no cell moves).
* `Game.PHom.hideCells`: function-only observation hides the cell moves.

`Silmaril.Games.Abstract.Cells.Thms` proves that the function-only models
embed, that hiding the cells recovers them exactly, and that observing
exported state is strictly finer than function-only observation.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u

/-- Moves of a game with exported cells. -/
inductive CMove (G : Game.{u}) (N : Type u) (V : N → Type u) : Type u
  /-- A move of `G`. -/
  | op (m : G.Move)
  /-- The environment reads cell `n`. -/
  | get (n : N)
  /-- The component answers a read of cell `n` with `v`. -/
  | got (n : N) (v : V n)
  /-- The environment writes `v` into cell `n`. -/
  | set (n : N) (v : V n)

namespace CMove

variable {G : Game.{u}} {N : Type u} {V : N → Type u}

/-- The move of `G`, if any. -/
def opOf : CMove G N V → Option G.Move
  | .op m => some m
  | _ => none

/-- The cell protocol, from a pending read (`some n`) or none: a read is
answered at once by a value of the same cell. -/
def CellOK : Option N → List (CMove G N V) → Prop
  | _, [] => True
  | none, .get n :: s => CellOK (some n) s
  | none, .got _ _ :: _ => False
  | none, .op _ :: s => CellOK none s
  | none, .set _ _ :: s => CellOK none s
  | some n, .got n' _ :: s => n' = n ∧ CellOK none s
  | some _, _ :: _ => False

theorem CellOK.of_prefix {p : Option N} {s t : List (CMove G N V)} (h : CellOK p t)
    (hst : s <+: t) : CellOK p s := by
  obtain ⟨r, rfl⟩ := hst
  induction s generalizing p with
  | nil => cases p <;> trivial
  | cons x s ih =>
    cases p <;> cases x <;> simp_all [CellOK, List.cons_append]

end CMove

namespace Game

variable (G : Game.{u}) (N : Type u) (V : N → Type u)

/-- A game with exported cells. -/
abbrev withCells : Game.{u} where
  Move := CMove G N V
  IsO
    | .op m => G.IsO m
    | .get _ => True
    | .got _ _ => False
    | .set _ _ => True
  Legal := {s | s.filterMap CMove.opOf ∈ G.Legal ∧ CMove.CellOK none s}
  nil_legal := ⟨G.nil_legal, trivial⟩
  legal_of_prefix := fun ⟨h₁, h₂⟩ h => ⟨G.legal_of_prefix h₁ (h.filterMap _), h₂.of_prefix h⟩

variable {G N V}

theorem filterMap_opOf_map_op (s : List G.Move) :
    (s.map (CMove.op (N := N) (V := V))).filterMap CMove.opOf = s := by
  induction s <;> simp_all [CMove.opOf]

theorem cellOK_map_op (s : List G.Move) : CMove.CellOK none (s.map (CMove.op (N := N) (V := V))) := by
  induction s <;> simp_all [CMove.CellOK]

/-- The function-only game embeds: no cell moves. -/
def Hom.ops : G.Hom (G.withCells N V) where
  map := CMove.op
  legal h := ⟨(filterMap_opOf_map_op _).symm ▸ h, cellOK_map_op _⟩
  isO h := h

/-- Function-only observation: hide the cell moves. -/
def PHom.hideCells : (G.withCells N V).PHom G where
  map := CMove.opOf
  legal h := h.1
  isO {m n} h ho := by cases m <;> cases h; exact ho

end Game

end Silmaril.Games.Abstract
