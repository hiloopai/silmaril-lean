module

public import Silmaril.Games.Reduct.Defs
public import Silmaril.Games.Institution.Thms
import Silmaril.Proofs.Games.Reduct.Sound
import Silmaril.Proofs.Games.Reduct.Complete
import Silmaril.Proofs.Games.Reduct.Pos

/-!
# The plays of a reduct: theorems

* `Game.mem_reduct_iff_rel`: **the plays of `Game.reduct f σ` are exactly the legal
  `Game.Rel f`-images of the plays of `σ`.** This describes both halves of the reduct: the lower
  forwarding along `f.lo` and the restriction along `f.up`.
* `Strategy.restrict_complete` (**the converse of `Strategy.restrict_sound`**): a legal
  `UpRel ρ`-image of a play of `σ` is a play of `σ.restrict ρ`. With the soundness direction
  `Strategy.restrict_sound'` (no trailing question) it gives `Strategy.mem_restrict_iff`.
* `Game.rel_comp`, `Game.rel_decomp`, `Game.forall₂_rel_id_iff`: the move relations are
  functorial; `Game.legal_mid`: the middle of two images of legal plays is legal;
  `Game.run_of_rel`: images of running plays are running.
* `Strategy.legal_of_upRel`: the preimage of a legal play under `UpRel ρ` is legal.

Legality of the image is needed: when `ρ.op` is not injective, the image of a legal play can
answer a question other than the pending one. Proofs are in `Silmaril.Proofs.Games.Reduct`.
-/

@[expose] public section

namespace Silmaril.Games

universe u

open CategoryTheory Silmaril.Proofs.Games.Reduct

namespace Strategy

variable {X G F : Sig.{u}}

/-- **Soundness of restriction**, without a trailing question. -/
theorem restrict_sound' (σ : Strategy X F) (ρ : Sig.Hom G F) {p : List (Move X G)}
    (hp : p ∈ σ.restrict ρ) : ∃ s ∈ σ, List.Forall₂ (UpRel ρ) s p :=
  Silmaril.Proofs.Games.Reduct.restrict_sound' σ ρ hp

/-- **The converse of `restrict_sound`**: a legal image of a play of `σ` is a play of the
restriction. -/
theorem restrict_complete (σ : Strategy X F) (ρ : Sig.Hom G F) {s : List (Move X F)}
    {p : List (Move X G)} (hs : s ∈ σ) (hr : List.Forall₂ (UpRel ρ) s p) (hp : Legal p) :
    p ∈ σ.restrict ρ := by
  have h := reduct_complete (Sig.Hom.id X) ρ σ hs (forall₂_upRel hr) hp
  rwa [show Handler.ofHom (Sig.Hom.id X) = Handler.id X from rfl, ofHandler_id, id_comp] at h

/-- The preimage of a legal play under `UpRel ρ` is legal. -/
theorem legal_of_upRel {ρ : Sig.Hom G F} {s : List (Move X F)} {p : List (Move X G)}
    (hr : List.Forall₂ (UpRel ρ) s p) (hp : Legal p) : Legal s :=
  Silmaril.Proofs.Games.Reduct.legal_of_upRel ρ hr hp

/-- **The plays of a restriction** are the legal images of the plays of the strategy. -/
theorem mem_restrict_iff (σ : Strategy X F) (ρ : Sig.Hom G F) (p : List (Move X G)) :
    p ∈ σ.restrict ρ ↔ Legal p ∧ ∃ s ∈ σ, List.Forall₂ (UpRel ρ) s p :=
  ⟨fun hp => ⟨(σ.restrict ρ).legal hp, restrict_sound' σ ρ hp⟩,
    fun ⟨hp, _, hs, hr⟩ => restrict_complete σ ρ hs hr hp⟩

end Strategy

namespace Game

variable {G G' : Game.{u}}

/-- **The plays of a reduct** are exactly the legal `Rel f`-images of the plays of the model. -/
theorem mem_reduct_iff_rel (f : G ⟶ G') (σ : G'.Model) (p : List (Move G.E G.F)) :
    p ∈ reduct f σ ↔ Legal p ∧ ∃ s ∈ σ, List.Forall₂ (Rel f) s p :=
  ⟨fun hp => ⟨(reduct f σ).legal hp, reduct_sound f σ hp⟩,
    fun ⟨hp, _, hs, hr⟩ => reduct_complete f.lo f.up σ hs hr hp⟩

/-- Move relations compose along composites of game morphisms. -/
theorem rel_comp {G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') {s : List (Move G''.E G''.F)}
    {t : List (Move G'.E G'.F)} {p : List (Move G.E G.F)} (h₁ : List.Forall₂ (Rel g) s t)
    (h₂ : List.Forall₂ (Rel f) t p) : List.Forall₂ (Rel (f ≫ g)) s p :=
  forall₂_comp h₁ h₂

/-- Composite move relations decompose, move by move. -/
theorem rel_decomp_move {G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') {a : Move G''.E G''.F}
    {c : Move G.E G.F} (h : Rel (f ≫ g) a c) : ∃ b, Rel g a b ∧ Rel f b c :=
  redRel_decomp h

/-- Composite move relations decompose. -/
theorem rel_decomp {G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') {s : List (Move G''.E G''.F)}
    {p : List (Move G.E G.F)} (h : List.Forall₂ (Rel (f ≫ g)) s p) :
    ∃ t, List.Forall₂ (Rel g) s t ∧ List.Forall₂ (Rel f) t p :=
  forall₂_decomp h

/-- **The middle of two images of legal plays is legal.** -/
theorem legal_mid {G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') {s : List (Move G''.E G''.F)}
    {t : List (Move G'.E G'.F)} {p : List (Move G.E G.F)} (h₁ : List.Forall₂ (Rel g) s t)
    (h₂ : List.Forall₂ (Rel f) t p) (hs : Legal s) (hp : Legal p) : Legal t :=
  Silmaril.Proofs.Games.Reduct.legal_mid h₁ h₂ hs hp

/-- The move relation of the identity is equality. -/
theorem rel_id_iff (a b : Move G.E G.F) : Rel (𝟙 G) a b ↔ a = b := by
  constructor
  · intro h
    cases h <;> rfl
  · rintro rfl
    rcases a with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩)
    · exact .lask (lo := Sig.Hom.id G.E) (up := Sig.Hom.id G.F) m
    · exact .lans (lo := Sig.Hom.id G.E) (up := Sig.Hom.id G.F) m n
    · exact .uask (lo := Sig.Hom.id G.E) (up := Sig.Hom.id G.F) q
    · exact .uans (lo := Sig.Hom.id G.E) (up := Sig.Hom.id G.F) q n

/-- Plays related by the identity's move relation are equal. -/
theorem forall₂_rel_id_iff (s p : List (Move G.E G.F)) :
    List.Forall₂ (Rel (𝟙 G)) s p ↔ s = p := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hab _ ih => rw [(rel_id_iff _ _).1 hab, ih]
  · rintro rfl
    induction s with
    | nil => exact .nil
    | cons a s ih => exact .cons ((rel_id_iff a a).2 rfl) ih

/-- With an injective upper renaming, the image of a legal play is legal. -/
theorem legal_of_rel_inj (f : G ⟶ G') (hinj : Function.Injective f.up.op)
    {s : List (Move G'.E G'.F)} {p : List (Move G.E G.F)} (hr : List.Forall₂ (Rel f) s p)
    (hs : Legal s) : Legal p :=
  legal_of_inj hinj hr hs

/-- The image of a play ending in a running position ends in a running position. -/
theorem run_of_rel (f : G ⟶ G') {s : List (Move G'.E G'.F)} {p : List (Move G.E G.F)}
    (h : List.Forall₂ (Rel f) s p) {q' : G'.F.Op} (hs : Path .idle s (.run q')) (hp : Legal p) :
    ∃ q, Path .idle p (.run q) := by
  obtain ⟨y, hy⟩ := hp
  have hpos := redPos_path h .idle hs hy
  cases hpos with
  | run q => exact ⟨q, hy⟩

end Game

end Silmaril.Games
