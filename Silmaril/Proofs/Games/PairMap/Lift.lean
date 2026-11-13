module

public import Silmaril.Games.Reduct.Thms

/-!
# Renaming the lower interface along the left injection: plays

`(ofHandler (ofHom (Sig.Hom.inl F₁ F₂))).comp τ` offers the operations of `τ : Strategy F₁ G`
over the lower interface `F₁ ⊕ₛ F₂`, calling only its left summand. Its plays are exactly the
plays of `τ` with every lower move renamed by `liftMove` (`mem_lift_iff`): it is the reduct of
`τ` along the game morphism `liftHom` (`Game.mem_reduct_iff_rel`), whose move relation is the
graph of `liftMove` (`rel_iff`).

Proofs for `Silmaril.Games.PairMap.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.PairMap

open Silmaril.Games CategoryTheory

universe u

variable {E F₁ F₂ G : Sig.{u}}

/-- A move of `F₁ ↠ G` seen in `F₁ ⊕ₛ F₂ ↠ G`: lower operations go to the left summand. -/
def liftMove (F₂ : Sig.{u}) : Move F₁ G → Move (F₁ ⊕ₛ F₂) G
  | .inl (.ask m) => .inl (.ask (.inl m))
  | .inl (.ans m n) => .inl (.ans (.inl m) n)
  | .inr e => .inr e

theorem liftMove_injective : Function.Injective (liftMove (F₁ := F₁) (G := G) F₂) := by
  intro a b h
  rcases a with (⟨m⟩ | ⟨m, n⟩) | e <;> rcases b with (⟨m'⟩ | ⟨m', n'⟩) | e' <;> cases h <;> rfl

/-- The game morphism renaming the lower interface along the left injection. -/
def liftHom (F₁ F₂ G : Sig.{u}) : (Game.mk (F₁ ⊕ₛ F₂) G) ⟶ (Game.mk F₁ G) :=
  ⟨Sig.Hom.inl F₁ F₂, Sig.Hom.id G⟩

theorem reduct_liftHom (τ : Strategy F₁ G) :
    Game.reduct (liftHom F₁ F₂ G) τ =
      (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ := by
  show (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp
    (τ.restrict (Sig.Hom.id G)) = _
  rw [Strategy.restrict_id]

/-- The move relation of `liftHom` is the graph of `liftMove`. -/
theorem rel_iff (a : Move F₁ G) (b : Move (F₁ ⊕ₛ F₂) G) :
    Game.Rel (liftHom F₁ F₂ G) a b ↔ b = liftMove F₂ a := by
  constructor
  · intro h
    cases h <;> rfl
  · rintro rfl
    rcases a with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩)
    · exact RedRel.lask (lo := Sig.Hom.inl F₁ F₂) (up := Sig.Hom.id G) m
    · exact RedRel.lans (lo := Sig.Hom.inl F₁ F₂) (up := Sig.Hom.id G) m n
    · exact RedRel.uask (lo := Sig.Hom.inl F₁ F₂) (up := Sig.Hom.id G) q
    · exact RedRel.uans (lo := Sig.Hom.inl F₁ F₂) (up := Sig.Hom.id G) q n

theorem forall₂_rel_iff (s : List (Move F₁ G)) (p : List (Move (F₁ ⊕ₛ F₂) G)) :
    List.Forall₂ (Game.Rel (liftHom F₁ F₂ G)) s p ↔ p = s.map (liftMove F₂) := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hab _ ih => rw [List.map_cons, ← ih, ← (rel_iff _ _).1 hab]
  · rintro rfl
    induction s with
    | nil => exact .nil
    | cons a s ih => exact .cons ((rel_iff a _).2 rfl) ih

/-- **The plays of `τ` seen over `F₁ ⊕ₛ F₂`** are the renamed plays of `τ`. -/
theorem mem_lift_iff (τ : Strategy F₁ G) (p : List (Move (F₁ ⊕ₛ F₂) G)) :
    p ∈ (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ ↔
      ∃ s ∈ τ, p = s.map (liftMove F₂) := by
  rw [← reduct_liftHom, Game.mem_reduct_iff_rel]
  constructor
  · rintro ⟨-, s, hs, hr⟩
    exact ⟨s, hs, (forall₂_rel_iff s p).1 hr⟩
  · rintro ⟨s, hs, hp⟩
    have hr : List.Forall₂ (Game.Rel (liftHom F₁ F₂ G)) s p := (forall₂_rel_iff s p).2 hp
    exact ⟨Game.legal_of_rel_inj _ (fun _ _ h => h) hr (τ.legal hs), s, hs, hr⟩

theorem mem_map_lift {τ : Strategy F₁ G} {y : List (Move F₁ G)} (hy : y ∈ τ) :
    y.map (liftMove F₂) ∈ (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ :=
  (mem_lift_iff τ _).2 ⟨y, hy, rfl⟩

/-- A one-move extension of a renamed play is the renaming of a one-move extension. -/
theorem of_mem_snoc {τ : Strategy F₁ G} {y : List (Move F₁ G)} {o' : Move (F₁ ⊕ₛ F₂) G}
    (h : y.map (liftMove F₂) ++ [o'] ∈
      (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ) :
    ∃ o, o' = liftMove F₂ o ∧ y ++ [o] ∈ τ := by
  obtain ⟨s, hs, he⟩ := (mem_lift_iff τ _).1 h
  obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 he.symm
  have hs₁ : s₁ = y := (List.map_inj_right fun _ _ h => liftMove_injective h).1 h₁
  obtain ⟨o, rfl, ho⟩ := List.map_eq_singleton_iff.1 h₂
  exact ⟨o, ho.symm, hs₁ ▸ hs⟩

/-! ## Inverting `liftMove` on given moves -/

theorem liftMove_eq_inr {o : Move F₁ G} {e : Ev G}
    (h : (.inr e : Move (F₁ ⊕ₛ F₂) G) = liftMove F₂ o) : o = .inr e := by
  rcases o with (⟨m⟩ | ⟨m, n⟩) | e' <;> cases h
  rfl

theorem liftMove_eq_askL {o : Move F₁ G} {f : F₁.Op}
    (h : (.inl (.ask (.inl f)) : Move (F₁ ⊕ₛ F₂) G) = liftMove F₂ o) : o = .inl (.ask f) := by
  rcases o with (⟨m⟩ | ⟨m, n⟩) | e' <;> cases h
  rfl

theorem liftMove_ne_askR {o : Move F₁ G} {q : F₂.Op}
    (h : (.inl (.ask (.inr q)) : Move (F₁ ⊕ₛ F₂) G) = liftMove F₂ o) : False := by
  rcases o with (⟨m⟩ | ⟨m, n⟩) | e' <;> cases h

theorem liftMove_eq_ansL {o : Move F₁ G} {f : F₁.Op} {r : F₁.Ar f}
    (h : (.inl (.ans (.inl f) r) : Move (F₁ ⊕ₛ F₂) G) = liftMove F₂ o) : o = .inl (.ans f r) := by
  rcases o with (⟨m⟩ | ⟨m, n⟩) | e' <;> cases h
  rfl

/-- A move after a play has a legal transition from the play's position. -/
theorem step_of_snoc {X Y : Sig.{u}} {σ : Strategy X Y} {x : List (Move X Y)} {o : Move X Y}
    {p : Pos X Y}
    (h : x ++ [o] ∈ σ) (hp : Path .idle x p) : ∃ p', Step p o p' := by
  obtain ⟨_, hl⟩ := σ.legal h
  obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hl
  cases hy.det hp
  exact ⟨_, hst⟩

end Silmaril.Proofs.Games.PairMap
