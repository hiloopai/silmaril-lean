module

public import Silmaril.Games.Reduct.Thms
public import Silmaril.Games.Div.Defs
import Silmaril.Proofs.Games.DInstitution.Reduct

/-!
# The institution of divergence-observing game semantics

`DGInst : Inst.{1, 0, 0, 0, 0}` is `GInst` (`Silmaril.Games.Institution.Defs`) with
divergence-observing strategies (`DStrategy`, `Silmaril.Games.Div.Defs`) as models. Signatures and
signature morphisms are those of `GInst` (games and lens-like game morphisms).

* **Reduct** `DStrategy.reduct f δ`. Its finite plays are `Game.reduct f δ.toStrategy`, i.e. the
  legal `Game.Rel f`-images of the plays of `δ` (`Game.mem_reduct_iff_rel`). Its divergences are
  the legal images of the divergences of `δ`. Its infinite plays are the infinite plays all of
  whose prefixes are plays of the reduct and are images of the prefixes of one infinite play of
  `δ`. The reduct is strictly functorial (`DStrategy.reduct_id`, `DStrategy.reduct_comp`); the
  infinite-play half of `reduct_comp` chooses the middle infinite play index by index
  (`Silmaril.Proofs.Games.DInstitution.inf_mid`).
* **Sentences** `DGSen E F`: properties of divergence-observing strategies, translated by
  evaluating on the reduct; `divPlay p` ("may diverge after `p`") is the divergence test.
* `GInst.toDGInst : Inst.CoHom GInst DGInst`: a `GInst` sentence is a `DGInst` sentence about the
  finite plays, and a divergence-observing strategy is read as its finite plays (`forget`). The
  square commutes because the finite plays of the reduct are the reduct of the finite plays
  (`DStrategy.forget_reduct`, by definition).

**Relation to the design.** `docs/projects/spectec/README.md` §2 planned the reduct as the composite
`(DStrategy.ofHandler (ofHom f.lo)).comp (δ.comp (DStrategy.ofHandler (ofHom f.up)))`, with
functoriality from that of `DStrategy.ofHandler` on infinite plays. Here the reduct is given
directly by the move relation `Game.Rel f`, which the finite case shows to be the play-level
content of the forwarding composite (`Game.mem_reduct_iff_rel`). That the divergences and
infinite plays of the forwarding composite are the ones above is not proved.

New definitions.
-/

@[expose] public section

namespace Silmaril.Games

open CategoryTheory Silmaril.Logic.Institution

universe u

namespace DStrategy

variable {G G' G'' : Game.{u}}

/-- **The reduct of a divergence-observing strategy** along a game morphism. -/
def reduct (f : G ⟶ G') (δ : DStrategy G'.E G'.F) : DStrategy G.E G.F where
  toStrategy := Game.reduct f δ.toStrategy
  div := {p | Legal p ∧ ∃ s ∈ δ.div, List.Forall₂ (Game.Rel f) s p}
  inf := {I | IsInfPlay I ∧ I ⊆ (Game.reduct f δ.toStrategy).plays ∧
    ∃ J ∈ δ.inf, ∀ p ∈ I, ∃ s ∈ J, List.Forall₂ (Game.Rel f) s p}
  div_mem := fun ⟨hp, s, hs, hr⟩ =>
    (Game.mem_reduct_iff_rel f _ _).2 ⟨hp, s, δ.div_mem hs, hr⟩
  div_run := fun ⟨hp, _, hs, hr⟩ =>
    let ⟨_, hq⟩ := δ.div_run hs
    Game.run_of_rel f hr hq hp
  inf_isInf h := h.1
  inf_sub h := h.2.1

/-- The finite plays of the reduct are the reduct of the finite plays. -/
@[simp] theorem forget_reduct (f : G ⟶ G') (δ : DStrategy G'.E G'.F) :
    (reduct f δ).forget = Game.reduct f δ.forget := rfl

/-- The divergences of the reduct are the legal images of the divergences. -/
theorem mem_div_reduct (f : G ⟶ G') (δ : DStrategy G'.E G'.F) (p : List (Move G.E G.F)) :
    p ∈ (reduct f δ).div ↔ Legal p ∧ ∃ s ∈ δ.div, List.Forall₂ (Game.Rel f) s p := Iff.rfl

/-- The reduct along the identity is the identity. -/
theorem reduct_id (δ : DStrategy G.E G.F) : reduct (𝟙 G) δ = δ :=
  Silmaril.Proofs.Games.DInstitution.reduct_id δ

/-- **The reduct along a composite is the composite of the reducts.** -/
theorem reduct_comp (f : G ⟶ G') (g : G' ⟶ G'') (δ : DStrategy G''.E G''.F) :
    reduct (f ≫ g) δ = reduct f (reduct g δ) :=
  Silmaril.Proofs.Games.DInstitution.reduct_comp f g δ

/-- The reduct is monotone. -/
theorem reduct_mono (f : G ⟶ G') {δ δ' : DStrategy G'.E G'.F} (h : δ ≤ δ') :
    reduct f δ ≤ reduct f δ' :=
  ⟨Game.reduct_mono f h.1, fun _ ⟨hp, s, hs, hr⟩ => ⟨hp, s, h.2.1 hs, hr⟩,
    fun _ ⟨hI, hsub, J, hJ, hrel⟩ =>
      ⟨hI, fun _ hp => Game.reduct_mono f h.1 (hsub hp), J, h.2.2 hJ, hrel⟩⟩

end DStrategy

/-! ## Sentences -/

/-- A sentence about divergence-observing strategies of `E ↠ F`. -/
@[ext] structure DGSen (E F : Sig.{u}) : Type u where
  /-- The strategies satisfying the sentence. -/
  holds : DStrategy E F → Prop

namespace DGSen

variable {E F : Sig.{u}}

/-- A `GInst` sentence, about the finite plays. -/
def ofGSen (φ : GSen E F) : DGSen E F := ⟨fun δ => φ.holds δ.toStrategy⟩

/-- `δ` may diverge after `p`. -/
def divPlay (p : List (Move E F)) : DGSen E F := ⟨fun δ => p ∈ δ.div⟩

/-- `δ` never diverges. -/
def divFree : DGSen E F := ⟨fun δ => δ.div = ∅⟩

end DGSen

namespace Game

variable {G G' : Game.{0}}

/-- Divergence-observing models of a game, with equalities as model morphisms. -/
def DDModel (G : Game.{0}) : Type := DStrategy G.E G.F

instance DDModel.category (G : Game.{0}) : Category.{0} G.DDModel where
  Hom σ τ := PLift (σ = τ)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- Sentence translation: evaluate on the reduct. -/
def dsenMap (f : G ⟶ G') (φ : DGSen G.E G.F) : DGSen G'.E G'.F :=
  ⟨fun δ => φ.holds (DStrategy.reduct f δ)⟩

/-- The reduct as a functor of discrete categories. -/
def dreductD (f : G ⟶ G') : G'.DDModel ⥤ G.DDModel where
  obj δ := DStrategy.reduct f δ
  map h := ⟨congrArg (DStrategy.reduct f) h.down⟩

/-- Reading a divergence-observing model as its finite plays. -/
def forgetD (G : Game.{0}) : G.DDModel ⥤ G.DModel where
  obj δ := (δ : DStrategy G.E G.F).toStrategy
  map h := ⟨congrArg DStrategy.toStrategy h.down⟩

end Game

namespace DGInst

open Game

/-- The room of a game. -/
def room (G : Game.{0}) : Room.{0, 0, 0} :=
  ⟨DGSen G.E G.F, Cat.of G.DDModel, fun δ φ => φ.holds δ⟩

/-- The corridor of a game morphism; the satisfaction condition holds by definition. -/
def corridor {G G' : Game.{0}} (f : G ⟶ G') : room G ⟶ room G' :=
  ⟨dsenMap f, dreductD f, fun _ _ => Iff.rfl⟩

theorem dsenMap_id (G : Game.{0}) : dsenMap (𝟙 G) = id :=
  funext fun φ => DGSen.ext (funext fun δ => by
    change φ.holds (DStrategy.reduct (𝟙 G) δ) = φ.holds δ
    rw [DStrategy.reduct_id])

theorem dsenMap_comp {G G' G'' : Game.{0}} (f : G ⟶ G') (g : G' ⟶ G'') :
    dsenMap (f ≫ g) = dsenMap g ∘ dsenMap f :=
  funext fun φ => DGSen.ext (funext fun δ => by
    change φ.holds (DStrategy.reduct (f ≫ g) δ) = φ.holds (DStrategy.reduct f (DStrategy.reduct g δ))
    rw [DStrategy.reduct_comp])

/-- The institution of divergence-observing game semantics, as a functor into rooms. -/
def institution : Game.{0} ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id G := Room.hom_ext (dsenMap_id G)
    (Functor.ext (fun δ => DStrategy.reduct_id δ) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (dsenMap_comp f g)
    (Functor.ext (fun δ => DStrategy.reduct_comp f g δ) (fun _ _ _ => rfl))

end DGInst

/-- **The institution of divergence-observing game semantics** `DGInst`: games,
divergence-observing strategies, and their properties. -/
def DGInst : Inst.{1, 0, 0, 0, 0} := ⟨Game.{0}, DGInst.institution⟩

/-- **`GInst` into `DGInst`**: `GInst` sentences are sentences about the finite plays, and a
divergence-observing strategy is read as its finite plays. -/
def GInst.toDGInst : Inst.CoHom GInst DGInst where
  Φ := 𝟭 _
  ρ :=
    { app := fun G => ⟨DGSen.ofGSen, Game.forgetD G, fun _ _ => Iff.rfl⟩
      naturality := fun _ _ _ =>
        Room.hom_ext rfl (Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

end Silmaril.Games
