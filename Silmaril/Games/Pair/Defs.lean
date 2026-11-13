module

public import Silmaril.Games.Strategy.Defs
public import Silmaril.Games.Split.Defs

/-!
# Pairing strategies

`σ₁.pair σ₂ : Strategy E (F₁ ⊕ₛ F₂)` offers the operations of both
`σ₁ : Strategy E F₁` and `σ₂ : Strategy E F₂`, sharing the lower interface
`E`. Each `F₁`-question is served by `σ₁` and each `F₂`-question by `σ₂`, each
component continuing from where its previous round ended; the two
components do not communicate. Its plays are the legal plays whose halves
(`Split.halves`) are plays of `σ₁` and `σ₂`.

This models a component exporting two independent sets of operations. Since
the game is single-threaded, rounds never overlap. It is the pairing for the
sum of signatures in the role of a product of objects; the universal property
(projections by restriction along `Sig.Hom.inl`/`Sig.Hom.inr`) is not proved
here.
-/

@[expose] public section

namespace Silmaril.Games

universe u

namespace Strategy

variable {E F₁ F₂ : Sig.{u}}

/-- Opponent moves after a play of `σ₁.pair σ₂` are accepted. -/
theorem pair_receptive (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂)
    {s : List (Move E (F₁ ⊕ₛ F₂))} {x y : Pos E (F₁ ⊕ₛ F₂)} {o : Move E (F₁ ⊕ₛ F₂)}
    (h₁ : (Split.halves false s).1 ∈ σ₁) (h₂ : (Split.halves false s).2 ∈ σ₂)
    (hx : Path .idle s x) (hxy : Step x o y) (ho : o.IsO) :
    (Split.halves false (s ++ [o])).1 ∈ σ₁ ∧ (Split.halves false (s ++ [o])).2 ∈ σ₂ := by
  obtain ⟨y₁, y₂, hp₁, hp₂, hr⟩ := Split.halves_path hx (Split.Rel.idle false)
  obtain ⟨c₁, c₂⟩ := Split.halves_concat false s o
  rw [c₁, c₂]
  generalize Split.side false s = b at hr
  cases hxy with
  | ask q =>
    cases hr
    rcases q with q | q
    · exact ⟨σ₁.receptive h₁ hp₁ (.ask q) trivial, by simpa [Split.halves] using h₂⟩
    · exact ⟨by simpa [Split.halves] using h₁, σ₂.receptive h₂ hp₂ (.ask q) trivial⟩
  | reply q m n =>
    cases hr with
    | waitL q m =>
      exact ⟨σ₁.receptive h₁ hp₁ (.reply q m n) trivial, by simpa [Split.halves] using h₂⟩
    | waitR q m =>
      exact ⟨by simpa [Split.halves] using h₁, σ₂.receptive h₂ hp₂ (.reply q m n) trivial⟩
  | call => exact ho.elim
  | ret => exact ho.elim

/-- The pairing of two strategies with a common lower interface. -/
def pair (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) : Strategy E (F₁ ⊕ₛ F₂) where
  plays := {p | Legal p ∧ (Split.halves false p).1 ∈ σ₁ ∧ (Split.halves false p).2 ∈ σ₂}
  nil_mem := ⟨Legal.nil, σ₁.nil_mem, σ₂.nil_mem⟩
  legal h := h.1
  of_prefix := fun ⟨hl, h₁, h₂⟩ hq =>
    ⟨hl.of_prefix hq, σ₁.of_prefix h₁ (Split.halves_prefix hq _).1,
      σ₂.of_prefix h₂ (Split.halves_prefix hq _).2⟩
  receptive := fun ⟨_, h₁, h₂⟩ hx hxy ho =>
    ⟨⟨_, hx.append (.single hxy)⟩, pair_receptive σ₁ σ₂ h₁ h₂ hx hxy ho⟩

/-- The plays of a pairing. -/
theorem mem_pair {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} {p : List (Move E (F₁ ⊕ₛ F₂))} :
    p ∈ σ₁.pair σ₂ ↔
      Legal p ∧ (Split.halves false p).1 ∈ σ₁ ∧ (Split.halves false p).2 ∈ σ₂ := Iff.rfl

/-- Pairing is monotone in both arguments. -/
theorem pair_mono {σ₁ τ₁ : Strategy E F₁} {σ₂ τ₂ : Strategy E F₂} (h₁ : σ₁ ≤ τ₁)
    (h₂ : σ₂ ≤ τ₂) : σ₁.pair σ₂ ≤ τ₁.pair τ₂ :=
  fun _ ⟨hl, hp₁, hp₂⟩ => ⟨hl, h₁ hp₁, h₂ hp₂⟩

end Strategy

end Silmaril.Games
