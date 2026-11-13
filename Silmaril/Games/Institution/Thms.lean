module

public import Silmaril.Games.Institution.Defs
public import Silmaril.Proofs.Games.Institution.Upper

/-!
# The institution of game semantics: theorems

* `GInst.sat_iff`: the satisfaction condition, in the form of the classic definition.
* `Game.sat_box_iff`, `Game.sat_dia_iff`: the play fragment of the satisfaction
  condition. A reduct satisfies `□ S` (`◇ T`) iff the model satisfies `□ (pull f S)`
  (`◇ (push f T)`). Both rest on `Game.mem_reduct_iff`, so the plays of the reduct are the
  image of the plays of the model.
* `Game.map_box`, `Game.map_dia`, `Game.map_and`, `Game.map_top`: the play fragment is
  closed under sentence translation.
* `GInst.refine`: universal sentences go down refinement and existential ones go up
  (`GSen.box_universal`, `GSen.dia_existential`); translation preserves both classes.
* `Strategy.restrict_sound` (the upper half of the reduct, one direction): every play of
  `σ.restrict ρ` is the `UpRel ρ`-image of a play of `σ`, possibly followed by one question not
  forwarded yet. `Game.reduct_id_lo` reduces a reduct with identity lower renaming to a
  restriction. Proofs are in `Silmaril.Proofs.Games.Institution.Upper`.
* `GInst.comp_sound`: composition of strategies is sound for safety. If `σ ⊨ □ S` and
  `τ ⊨ □ T`, then `σ.comp τ ⊨ □ (S ⋈ T)`, where `S ⋈ T` is the set of hidings of interactions
  of `S` with `T`. This is linking as composition (M3) at the level of the institution.
-/

@[expose] public section

namespace Silmaril.Games

open CategoryTheory Silmaril.Logic.Institution GSen

universe u

namespace Game

variable {G G' : Game.{u}}

/-- A reduct satisfies `□ S` iff the model satisfies `□ (pull f S)`. -/
theorem sat_box_iff (f : G ⟶ G') (σ : G'.Model) (S : Set (List (Move G.E G.F))) :
    (box S).holds (reduct f σ) ↔ (box (pull f S)).holds σ := by
  simp only [holds_box, pull, Set.mem_ofPred_eq]
  constructor
  · intro h s hs p hp
    exact h p ((mem_reduct_iff f σ p).2 ⟨s, hs, hp⟩)
  · intro h p hp
    obtain ⟨s, hs, hp⟩ := (mem_reduct_iff f σ p).1 hp
    exact h s hs p hp

/-- A reduct satisfies `◇ T` iff the model satisfies `◇ (push f T)`. -/
theorem sat_dia_iff (f : G ⟶ G') (σ : G'.Model) (T : Set (List (Move G.E G.F))) :
    (dia T).holds (reduct f σ) ↔ (dia (push f T)).holds σ := by
  simp only [holds_dia, push, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hpT, hp⟩
    obtain ⟨s, hs, hp⟩ := (mem_reduct_iff f σ p).1 hp
    exact ⟨s, ⟨p, hpT, hp⟩, hs⟩
  · rintro ⟨s, ⟨p, hpT, hp⟩, hs⟩
    exact ⟨p, hpT, (mem_reduct_iff f σ p).2 ⟨s, hs, hp⟩⟩

/-- Translating `□ S` gives `□ (pull f S)`. -/
theorem map_box (f : G ⟶ G') (S : Set (List (Move G.E G.F))) :
    senMap f (box S) = box (pull f S) :=
  GSen.ext (funext fun σ => propext (sat_box_iff f σ S))

/-- Translating `◇ T` gives `◇ (push f T)`. -/
theorem map_dia (f : G ⟶ G') (T : Set (List (Move G.E G.F))) :
    senMap f (dia T) = dia (push f T) :=
  GSen.ext (funext fun σ => propext (sat_dia_iff f σ T))

/-- Translation commutes with conjunction. -/
theorem map_and (f : G ⟶ G') (φ ψ : GSen G.E G.F) :
    senMap f (φ.and ψ) = (senMap f φ).and (senMap f ψ) := rfl

/-- Translation preserves truth. -/
theorem map_top (f : G ⟶ G') : senMap f (GSen.top : GSen G.E G.F) = GSen.top := rfl

/-- Translation preserves universal sentences. -/
theorem universal_senMap (f : G ⟶ G') {φ : GSen G.E G.F} (h : φ.Universal) :
    (senMap f φ).Universal := fun _ _ hστ hτ => h (reduct_mono f hστ) hτ

/-- Translation preserves existential sentences. -/
theorem existential_senMap (f : G ⟶ G') {φ : GSen G.E G.F} (h : φ.Existential) :
    (senMap f φ).Existential := fun _ _ hστ hσ => h (reduct_mono f hστ) hσ

end Game

namespace Strategy

/-- **Soundness of restriction** (upper half of the reduct): every play of `σ.restrict ρ` is
the image under `UpRel ρ` of a play of `σ`, possibly followed by one question that has not
been forwarded yet. -/
theorem restrict_sound {X G F : Sig.{u}} (σ : Strategy X F) (ρ : Sig.Hom G F)
    {p : List (Move X G)} (hp : p ∈ σ.restrict ρ) :
    ∃ s ∈ σ, List.Forall₂ (UpRel ρ) s p ∨
      ∃ p' q, p = p' ++ [.inr (.ask q)] ∧ List.Forall₂ (UpRel ρ) s p' :=
  Silmaril.Proofs.Games.Institution.restrict_sound σ ρ hp

end Strategy

namespace Game

/-- A reduct whose lower renaming is the identity is a restriction. -/
theorem reduct_id_lo {E F F' : Sig.{u}} (up : Sig.Hom F F') (σ : Strategy E F') :
    reduct (G := ⟨E, F⟩) (G' := ⟨E, F'⟩) ⟨Sig.Hom.id E, up⟩ σ = σ.restrict up := by
  change (Strategy.ofHandler (Handler.ofHom (Sig.Hom.id E))).comp (σ.restrict up) = _
  rw [show Handler.ofHom (Sig.Hom.id E) = Handler.id E from rfl, Strategy.ofHandler_id,
    Strategy.id_comp]

end Game

namespace GSen

variable {E F : Sig.{u}}

/-- `□ S` is universal. -/
theorem box_universal (S : Set (List (Move E F))) : (box S).Universal :=
  fun _ _ h hτ s hs => hτ s (h hs)

/-- `◇ T` is existential. -/
theorem dia_existential (T : Set (List (Move E F))) : (dia T).Existential :=
  fun _ _ h ⟨s, hsT, hs⟩ => ⟨s, hsT, h hs⟩

/-- **Safety of a transition system**: if `S` is closed under prefixes and under Opponent
moves and contains the traces of `L`, then the strategy of `L` satisfies `□ S`. -/
theorem box_ofLTS {L : LTS E F} {S : Set (List (Move E F))}
    (hpre : ∀ ⦃s t⦄, t ∈ S → s <+: t → s ∈ S)
    (hO : ∀ ⦃s : List (Move E F)⦄ ⦃o : Move E F⦄, s ∈ S → o.IsO → s ++ [o] ∈ S)
    (htr : L.Traces ⊆ S) : (box S).holds (Strategy.ofLTS L) := by
  rintro p ⟨-, s, hs, hp⟩
  have hsS : s ∈ S := by
    rcases hs with rfl | ⟨hs, -⟩
    · exact htr ⟨_, .nil _⟩
    · exact htr hs
  rcases hp with hp | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact hpre hsS hp
  · exact hO (hpre hsS hp₀) ho

/-- Conjunctions of universal sentences are universal. -/
theorem Universal.and {φ ψ : GSen E F} (hφ : φ.Universal) (hψ : ψ.Universal) :
    (φ.and ψ).Universal := fun _ _ h ⟨h₁, h₂⟩ => ⟨hφ h h₁, hψ h h₂⟩

/-- Conjunctions of existential sentences are existential. -/
theorem Existential.and {φ ψ : GSen E F} (hφ : φ.Existential) (hψ : ψ.Existential) :
    (φ.and ψ).Existential := fun _ _ h ⟨h₁, h₂⟩ => ⟨hφ h h₁, hψ h h₂⟩

/-- The interactions of plays in `S` with plays in `T`, with the middle interface hidden. -/
def zipSet {G : Sig.{u}} (S : Set (List (Move E F))) (T : Set (List (Move F G))) :
    Set (List (Move E G)) :=
  {p | ∃ s ∈ S, ∃ t ∈ T, Zip s t p}

end GSen

namespace GInst

open Game

/-- **The satisfaction condition of `GInst`**, in the form of the classic definition. -/
theorem sat_iff {G G' : Game.{0}} (f : G ⟶ G') (σ : G'.Model) (φ : GSen G.E G.F) :
    (GInst.I.obj G').Sat σ ((GInst.I.map f).sen φ) ↔
      (GInst.I.obj G).Sat ((GInst.I.map f).mod.obj σ) φ :=
  (GInst.I.map f).sat σ φ

/-- **Refinement transfer**: universal sentences go down refinement and existential ones go
up. -/
theorem refine {E F : Sig.{u}} {σ τ : Strategy E F} (h : σ ≤ τ) :
    (∀ S, (box S).holds τ → (box S).holds σ) ∧ (∀ T, (dia T).holds σ → (dia T).holds τ) :=
  ⟨fun S => box_universal S h, fun T => dia_existential T h⟩

/-- **Composition is sound for safety** (linking as composition). -/
theorem comp_sound {E F G : Sig.{u}} {σ : Strategy E F} {τ : Strategy F G}
    {S : Set (List (Move E F))} {T : Set (List (Move F G))} (hσ : (box S).holds σ)
    (hτ : (box T).holds τ) : (box (zipSet S T)).holds (σ.comp τ) := by
  rintro p ⟨s, hs, t, ht, hz⟩
  exact ⟨s, hσ s hs, t, hτ t ht, hz⟩

/-- Composition preserves test witnesses: an interaction of a play of `σ` with a play of `τ`
is a play of the composite. -/
theorem comp_dia {E F G : Sig.{u}} {σ : Strategy E F} {τ : Strategy F G}
    {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)} (hσ : (diaPlay s).holds σ)
    (hτ : (diaPlay t).holds τ) (hz : Zip s t p) : (diaPlay p).holds (σ.comp τ) := by
  rw [holds_diaPlay] at *
  exact ⟨s, hσ, t, hτ, hz⟩

end GInst

end Silmaril.Games
