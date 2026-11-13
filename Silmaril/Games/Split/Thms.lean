module

public import Silmaril.Games.Split.Defs
public import Silmaril.Games.Play.Thms

/-!
# Splitting a play: theorems

The halves of a legal play are legal (`halves_path` and the other splitting lemmas are in
`Silmaril.Games.Split.Defs`).
-/

public section

namespace Silmaril.Games.Split

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- The halves of a legal play are legal. -/
theorem halves_legal {p : List (Move E (F₁ ⊕ₛ F₂))} (h : Legal p) :
    Legal (halves false p).1 ∧ Legal (halves false p).2 := by
  obtain ⟨_, h⟩ := h
  obtain ⟨y₁, y₂, h₁, h₂, -⟩ := halves_path h (Rel.idle false)
  exact ⟨⟨y₁, h₁⟩, ⟨y₂, h₂⟩⟩

end Silmaril.Games.Split
