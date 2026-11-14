module

public import Silmaril.Games.Abstract.Link.Defs
public import Silmaril.Games.Abstract.SigBridge.Defs
public import Silmaril.Games.Composition.Defs

/-!
# Composition of `E ↠ F` and `F ↠ G` as a linking situation

The joint moves are events at the three interfaces, `Ev E ⊕ Ev F ⊕ Ev G`.

* The lower component `E ↠ F` sees the events at `E` and `F`.
* The upper component `F ↠ G` sees the events at `F` and `G`.
* The environment sees the events at `E` and `G`.

Events at `F` are internal: both components see them (synchronisation) and
the environment does not (hiding). A joint play is legal when both views are
legal. Opponent moves of the composite are answers at `E` and questions at
`G`.

`Silmaril.Games.Abstract.SigLink.Thms` proves that generic linking in this
situation is the existing composition `Strategy.comp`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

namespace SigLink

variable {E F G : Sig.{u}}

/-- The lower component's view. -/
def p₁ : Ev E ⊕ Ev F ⊕ Ev G → Option (Move E F)
  | .inl a => some (.inl a)
  | .inr (.inl b) => some (.inr b)
  | .inr (.inr _) => none

/-- The upper component's view. -/
def p₂ : Ev E ⊕ Ev F ⊕ Ev G → Option (Move F G)
  | .inl _ => none
  | .inr (.inl b) => some (.inl b)
  | .inr (.inr c) => some (.inr c)

/-- The environment's view. -/
def pe : Ev E ⊕ Ev F ⊕ Ev G → Option (Move E G)
  | .inl a => some (.inl a)
  | .inr (.inl _) => none
  | .inr (.inr c) => some (.inr c)

/-- Opponent moves of the composite: answers at `E` and questions at `G`. -/
def IsO : Ev E ⊕ Ev F ⊕ Ev G → Prop
  | .inl (.ans _ _) => True
  | .inr (.inr (.ask _)) => True
  | _ => False

/-- The three views of a joint play are zipped. -/
theorem zip_views (u : List (Ev E ⊕ Ev F ⊕ Ev G)) :
    Zip (u.filterMap p₁) (u.filterMap p₂) (u.filterMap pe) := by
  induction u with
  | nil => exact .nil
  | cons x u ih =>
    rcases x with a | b | c
    · exact .left a ih
    · exact .sync b ih
    · exact .right c ih

end SigLink

open SigLink in
/-- Composition of `E ↠ F` and `F ↠ G` as a linking situation. -/
def sigLink (E F G : Sig.{u}) : LinkSpec (sigGame E F) (sigGame F G) (sigGame E G) where
  L := {
    Move := Ev E ⊕ Ev F ⊕ Ev G
    IsO := IsO
    Legal := {u | Legal (u.filterMap p₁) ∧ Legal (u.filterMap p₂)}
    nil_legal := ⟨Legal.nil, Legal.nil⟩
    legal_of_prefix := fun ⟨h₁, h₂⟩ h => ⟨h₁.of_prefix (h.filterMap _), h₂.of_prefix (h.filterMap _)⟩ }
  π₁ := {
    map := p₁
    legal := fun h => h.1
    isO := fun {m n} h ho => by
      rcases m with (_ | _) | (_ | _) | (_ | _) <;> cases h <;> simp_all [IsO, Move.IsO, sigGame] }
  π₂ := {
    map := p₂
    legal := fun h => h.2
    isO := fun {m n} h ho => by
      rcases m with (_ | _) | (_ | _) | (_ | _) <;> cases h <;> simp_all [IsO, Move.IsO, sigGame] }
  ext := {
    map := pe
    legal := fun h => Strategy.legal_of_zip h.1 h.2 (zip_views _)
    isO := fun {m n} h ho => by
      rcases m with (_ | _) | (_ | _) | (_ | _) <;> cases h <;> simp_all [IsO, Move.IsO, sigGame] }

end Silmaril.Games.Abstract
