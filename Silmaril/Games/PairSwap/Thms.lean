module

public import Silmaril.Games.PairSwap.Defs
public import Silmaril.Games.Reduct.Thms

/-!
# Pairing is symmetric

* **`Strategy.pair_restrict_swap`**: `(σ₁.pair σ₂).restrict (Sig.Hom.swap F₁ F₂) = σ₂.pair σ₁`.
  Offering `F₂ ⊕ₛ F₁` through `σ₁.pair σ₂` by exchanging the summands is the pairing in the
  other order.
* `Strategy.pair_comp_ofHom_swap`: the same, as a composition with the forwarding handler.

The proof is at the level of plays (`Strategy.mem_restrict_iff`): the only preimage of a play
`p` under `UpRel (Sig.Hom.swap F₁ F₂)` is `p.map Split.swapMove` (`eq_map_swapMove`), and its
halves are those of `p`, exchanged (`halves_map_swapMove`). The starting side of `halves` does
not matter for a legal play, which starts with a question (`halves_true_of_legal`).
-/

public section

namespace Silmaril.Games

universe u

namespace Split

variable {E F₁ F₂ : Sig.{u}}

/-- A play is related to its swap. -/
theorem forall₂_swapMove (p : List (Move E (F₂ ⊕ₛ F₁))) :
    List.Forall₂ (UpRel (Sig.Hom.swap F₁ F₂)) (p.map swapMove) p := by
  induction p with
  | nil => exact .nil
  | cons o p ih =>
    refine .cons ?_ ih
    match o with
    | .inl e => exact UpRel.low e
    | .inr (.ask (.inl q)) => exact UpRel.ask (X := E) (ρ := Sig.Hom.swap F₁ F₂) (Sum.inl q)
    | .inr (.ask (.inr q)) => exact UpRel.ask (X := E) (ρ := Sig.Hom.swap F₁ F₂) (Sum.inr q)
    | .inr (.ans (.inl q) r) => exact UpRel.ans (X := E) (ρ := Sig.Hom.swap F₁ F₂) (Sum.inl q) r
    | .inr (.ans (.inr q) r) => exact UpRel.ans (X := E) (ρ := Sig.Hom.swap F₁ F₂) (Sum.inr q) r

/-- The swap is the only preimage. -/
theorem eq_map_swapMove {s : List (Move E (F₁ ⊕ₛ F₂))} {p : List (Move E (F₂ ⊕ₛ F₁))}
    (h : List.Forall₂ (UpRel (Sig.Hom.swap F₁ F₂)) s p) : s = p.map swapMove := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    rw [List.map_cons, ih]
    congr 1
    cases hr with
    | low e => rfl
    | ask q => rcases q with q | q <;> rfl
    | ans q n => rcases q with q | q <;> rfl

/-- The halves of a swapped play are the halves of the play, exchanged. -/
theorem halves_map_swapMove : ∀ (b : Bool) (p : List (Move E (F₂ ⊕ₛ F₁))),
    halves b (p.map swapMove) = ((halves (!b) p).2, (halves (!b) p).1)
  | b, [] => by cases b <;> rfl
  | false, .inl e :: p => by
    simp only [List.map_cons, swapMove, halves, halves_map_swapMove false p, Bool.not_false]
  | true, .inl e :: p => by
    simp only [List.map_cons, swapMove, halves, halves_map_swapMove true p, Bool.not_true]
  | b, .inr (.ask (.inl q)) :: p => by
    cases b <;> simp only [List.map_cons, swapMove, halves, halves_map_swapMove true p,
      Bool.not_true]
  | b, .inr (.ask (.inr q)) :: p => by
    cases b <;> simp only [List.map_cons, swapMove, halves, halves_map_swapMove false p,
      Bool.not_false]
  | b, .inr (.ans (.inl q) r) :: p => by
    cases b <;> simp only [List.map_cons, swapMove, halves, halves_map_swapMove, Bool.not_true,
      Bool.not_false]
  | b, .inr (.ans (.inr q) r) :: p => by
    cases b <;> simp only [List.map_cons, swapMove, halves, halves_map_swapMove, Bool.not_true,
      Bool.not_false]

/-- A legal play starts with a question, so its halves do not depend on the starting side. -/
theorem halves_true_of_legal {p : List (Move E (F₁ ⊕ₛ F₂))} (h : Legal p) :
    halves true p = halves false p := by
  obtain ⟨y, hp⟩ := h
  cases hp with
  | nil => rfl
  | cons st _ =>
    cases st with
    | ask q => rcases q with q | q <;> rfl

end Split

namespace Strategy

variable {E F₁ F₂ : Sig.{u}}

open Split in
/-- **Pairing is symmetric**: exchanging the summands of `σ₁.pair σ₂` gives `σ₂.pair σ₁`. -/
theorem pair_restrict_swap (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).restrict (Sig.Hom.swap F₁ F₂) = σ₂.pair σ₁ := by
  ext p
  rw [mem_restrict_iff, mem_pair]
  constructor
  · rintro ⟨hl, s, ⟨-, h₁, h₂⟩, hr⟩
    rw [eq_map_swapMove hr, halves_map_swapMove, Bool.not_false, halves_true_of_legal hl] at h₁ h₂
    exact ⟨hl, h₂, h₁⟩
  · rintro ⟨hl, h₂, h₁⟩
    refine ⟨hl, p.map swapMove, ⟨legal_of_upRel (forall₂_swapMove p) hl, ?_, ?_⟩,
      forall₂_swapMove p⟩
    · rw [halves_map_swapMove, Bool.not_false, halves_true_of_legal hl]
      exact h₁
    · rw [halves_map_swapMove, Bool.not_false, halves_true_of_legal hl]
      exact h₂

/-- Symmetry of pairing, as a composition with the forwarding handler. -/
theorem pair_comp_ofHom_swap (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).comp (ofHandler (Handler.ofHom (Sig.Hom.swap F₁ F₂))) = σ₂.pair σ₁ :=
  pair_restrict_swap σ₁ σ₂

end Strategy

end Silmaril.Games
