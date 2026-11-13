module

public import Silmaril.Games.Institution.Thms
public import Silmaril.Games.DInstitution.Defs
public import Silmaril.Games.Reindex.Defs
public import Silmaril.Logic.Institution.Borrowing
public import Silmaril.Logic.Inst.Defs

/-!
# A facade for the game institutions

`GInst`, `GInstRef` and `DGInst` (`Silmaril.Games.{Institution,DInstitution}.Defs`) are bundled
`Silmaril.Logic.Institution.Inst`s. Reading a satisfaction or a translation in them means unfolding
`GInst.I.obj`, `(GInst.I.map f).sen` and `(c.ρ.app S).mod.obj`. This module gives the names under
which these are read, and builders for the comorphisms that recur in the Wasm graph.

* **Unfolding lemmas** (`@[simp]`, all `rfl`): satisfaction is `GSen.holds`
  (`GInst.sat_iff_holds`, `GInstRef.sat_iff_holds`, `DGInst.sat_iff_holds`), sentence translation
  is `Game.senMap` / `Game.dsenMap` (`*.map_sen`), the reduct is `Game.reduct` /
  `DStrategy.reduct` (`*.map_mod_obj`). The comorphisms `GInstRef.toGInst`, `GInst.toDGInst`,
  `GInst.alongCoHom` and `GInst.reindex` get their `Φ`, sentence and model maps.
* **Satisfaction transfer** into the game institutions: `GInst.coHom_holds_iff` and
  `DGInst.coHom_holds_iff` read the satisfaction condition of any comorphism `A → GInst` as a
  statement about `GSen.holds`.
* **Builders.** A *game reading* `GInst.Reading A` of an institution `A` gives each signature a
  game (`game : A.Sign ⥤ Game`) and reads each strategy as an `A`-model (`mod`), naturally in the
  signature (`mod_reduct`). Its comorphism `Reading.coHom : Inst.CoHom A GInst` translates a
  sentence `φ` to the game property "the model read off `σ` satisfies `φ`". The satisfaction
  condition is then `Iff.rfl`, and naturality is `A`'s satisfaction condition plus `mod_reduct`.
  `Reading.modelExpansive` says the comorphism is model-expansive when every `mod` is surjective,
  and `Reading.precomp_coHom` that precomposing a reading with a comorphism `c` gives
  `c.comp r.coHom`. `DGInst.Reading` is the same for divergence-observing strategies, and
  `Game.DModel.functor_ext` (a functor out of a discrete model category is determined by its
  objects) makes their naturality proofs one line.
* **Model-expansiveness** of `GInstRef.toGInst` and `GInst.toDGInst`
  (`DStrategy.ofStrategy` is a section of `forget`).
* **Notation**: the canonical `σ ⊨ φ` of `Silmaril.Inst` (class `Silmaril.Inst.Satisfies`) for
  `φ.holds σ`, for both `GSen` and `DGSen` (`GSen.instSatisfies`, `DGSen.instSatisfies`;
  `simp` unfolds it by `GSen.satisfies_iff`, `DGSen.satisfies_iff`).

New definitions; nothing here changes the institutions themselves.
-/

@[expose] public section

namespace Silmaril.Games

open CategoryTheory Silmaril.Logic.Institution

universe u v w u' v'

/-! ## Notation -/

open scoped Silmaril.Inst

/-- Game properties: `σ ⊨ φ` is `φ.holds σ`. -/
instance GSen.instSatisfies {E F : Sig.{u}} : Silmaril.Inst.Satisfies (Strategy E F) (GSen E F) :=
  ⟨fun σ φ => φ.holds σ⟩

/-- Divergence-observing game properties: `δ ⊨ φ` is `φ.holds δ`. -/
instance DGSen.instSatisfies {E F : Sig.{0}} : Silmaril.Inst.Satisfies (DStrategy E F) (DGSen E F) :=
  ⟨fun δ φ => φ.holds δ⟩

/-- `σ ⊨ φ` for a strategy and a game property is `φ.holds σ`. -/
@[simp] theorem GSen.satisfies_iff {E F : Sig.{u}} (σ : Strategy E F) (φ : GSen E F) :
    σ ⊨ φ ↔ φ.holds σ := Iff.rfl

/-- `δ ⊨ φ` for a divergence-observing strategy and property is `φ.holds δ`. -/
@[simp] theorem DGSen.satisfies_iff {E F : Sig.{0}} (δ : DStrategy E F) (φ : DGSen E F) :
    δ ⊨ φ ↔ φ.holds δ := Iff.rfl

/-! ## Unfolding lemmas -/

namespace GInst

open Game

variable {G G' : Game.{0}}

/-- Satisfaction in `GInst` is `GSen.holds`. -/
@[simp] theorem sat_iff_holds (σ : G.Model) (φ : GSen G.E G.F) :
    (GInst.I.obj G).Sat σ φ ↔ φ.holds σ := Iff.rfl

/-- Sentence translation in `GInst` is `Game.senMap`. -/
@[simp] theorem map_sen (f : G ⟶ G') (φ : GSen G.E G.F) :
    (GInst.I.map f).sen φ = Game.senMap f φ := rfl

/-- The reduct of `GInst` is `Game.reduct`. -/
@[simp] theorem map_mod_obj (f : G ⟶ G') (σ : G'.Model) :
    (GInst.I.map f).mod.obj σ = Game.reduct f σ := rfl

/-- `Game.senMap` evaluates on the reduct. -/
@[simp] theorem holds_senMap (f : G ⟶ G') (φ : GSen G.E G.F) (σ : G'.Model) :
    (Game.senMap f φ).holds σ ↔ φ.holds (Game.reduct f σ) := Iff.rfl

end GInst

namespace GInstRef

variable {G G' : Game.{0}}

/-- Satisfaction in `GInstRef` is `GSen.holds`. -/
@[simp] theorem sat_iff_holds (σ : G.Model) (φ : GSen G.E G.F) :
    (GInstRef.I.obj G).Sat σ φ ↔ φ.holds σ := Iff.rfl

/-- Sentence translation in `GInstRef` is `Game.senMap`. -/
@[simp] theorem map_sen (f : G ⟶ G') (φ : GSen G.E G.F) :
    (GInstRef.I.map f).sen φ = Game.senMap f φ := rfl

/-- The reduct of `GInstRef` is `Game.reduct`. -/
@[simp] theorem map_mod_obj (f : G ⟶ G') (σ : G'.Model) :
    (GInstRef.I.map f).mod.obj σ = Game.reduct f σ := rfl

@[simp] theorem toGInst_Φ : GInstRef.toGInst.Φ = 𝟭 Game.{0} := rfl

@[simp] theorem toGInst_sen (G : Game.{0}) (φ : GSen G.E G.F) :
    (GInstRef.toGInst.ρ.app G).sen φ = φ := rfl

@[simp] theorem toGInst_mod_obj (G : Game.{0}) (σ : G.Model) :
    (GInstRef.toGInst.ρ.app G).mod.obj σ = σ := rfl

/-- `GInstRef.toGInst` is model-expansive: its model maps are identities on objects. -/
theorem toGInst_modelExpansive : GInstRef.toGInst.ModelExpansive :=
  fun _ σ => ⟨σ, rfl⟩

end GInstRef

namespace DGInst

variable {G G' : Game.{0}}

/-- Satisfaction in `DGInst` is `DGSen.holds`. -/
@[simp] theorem sat_iff_holds (δ : DStrategy G.E G.F) (φ : DGSen G.E G.F) :
    (DGInst.I.obj G).Sat δ φ ↔ φ.holds δ := Iff.rfl

/-- Sentence translation in `DGInst` is `Game.dsenMap`. -/
@[simp] theorem map_sen (f : G ⟶ G') (φ : DGSen G.E G.F) :
    (DGInst.I.map f).sen φ = Game.dsenMap f φ := rfl

/-- The reduct of `DGInst` is `DStrategy.reduct`. -/
@[simp] theorem map_mod_obj (f : G ⟶ G') (δ : DStrategy G'.E G'.F) :
    (DGInst.I.map f).mod.obj δ = DStrategy.reduct f δ := rfl

/-- `Game.dsenMap` evaluates on the reduct. -/
@[simp] theorem holds_dsenMap (f : G ⟶ G') (φ : DGSen G.E G.F) (δ : DStrategy G'.E G'.F) :
    (Game.dsenMap f φ).holds δ ↔ φ.holds (DStrategy.reduct f δ) := Iff.rfl

end DGInst

namespace GInst

@[simp] theorem toDGInst_Φ : GInst.toDGInst.Φ = 𝟭 Game.{0} := rfl

@[simp] theorem toDGInst_sen (G : Game.{0}) (φ : GSen G.E G.F) :
    (GInst.toDGInst.ρ.app G).sen φ = DGSen.ofGSen φ := rfl

@[simp] theorem toDGInst_mod_obj (G : Game.{0}) (δ : DStrategy G.E G.F) :
    (GInst.toDGInst.ρ.app G).mod.obj δ = δ.toStrategy := rfl

/-- `GInst.toDGInst` is model-expansive: `DStrategy.ofStrategy` is a section of `forget`. -/
theorem toDGInst_modelExpansive : GInst.toDGInst.ModelExpansive :=
  fun _ σ => ⟨DStrategy.ofStrategy σ, rfl⟩

variable {C : Type u} [Category.{v} C]

@[simp] theorem alongCoHom_Φ (Φ : C ⥤ Game.{0}) : (alongCoHom Φ).Φ = Φ := rfl

@[simp] theorem alongCoHom_sen (Φ : C ⥤ Game.{0}) (X : C) (φ : GSen (Φ.obj X).E (Φ.obj X).F) :
    ((alongCoHom Φ).ρ.app X).sen φ = φ := rfl

@[simp] theorem alongCoHom_mod_obj (Φ : C ⥤ Game.{0}) (X : C) (σ : (Φ.obj X).Model) :
    ((alongCoHom Φ).ρ.app X).mod.obj σ = σ := rfl

/-- `alongCoHom Φ` is model-expansive: its corridors are identities. -/
theorem alongCoHom_modelExpansive (Φ : C ⥤ Game.{0}) : (alongCoHom Φ).ModelExpansive :=
  fun _ σ => ⟨σ, rfl⟩

variable {D : Type u} [Category.{v} D] {Φ : C ⥤ Game.{0}} {Ψ : D ⥤ Game.{0}}

@[simp] theorem reindex_Φ (F : C ⥤ D) (α : Φ ⟶ F ⋙ Ψ) : (reindex F α).Φ = F := rfl

@[simp] theorem reindex_sen (F : C ⥤ D) (α : Φ ⟶ F ⋙ Ψ) (X : C)
    (φ : GSen (Φ.obj X).E (Φ.obj X).F) :
    ((reindex F α).ρ.app X).sen φ = Game.senMap (α.app X) φ := rfl

@[simp] theorem reindex_mod_obj (F : C ⥤ D) (α : Φ ⟶ F ⋙ Ψ) (X : C)
    (σ : (Ψ.obj (F.obj X)).Model) :
    ((reindex F α).ρ.app X).mod.obj σ = Game.reduct (α.app X) σ := rfl

end GInst

/-! ## Satisfaction transfer into the game institutions -/

namespace GInst

/-- **Satisfaction transfer along a comorphism into `GInst`**, read with `GSen.holds`: a strategy
has the translated property iff the model read off it satisfies the sentence. -/
theorem coHom_holds_iff {A : Inst.{u, v, 0, 0, 0}} (c : Inst.CoHom A GInst) (S : A.Sign)
    (σ : (c.Φ.obj S).Model) (φ : (A.I.obj S).Sen) :
    GSen.holds (E := (c.Φ.obj S).E) (F := (c.Φ.obj S).F) ((c.ρ.app S).sen φ) σ ↔
      (A.I.obj S).Sat ((c.ρ.app S).mod.obj σ) φ :=
  c.satisfaction S σ φ

end GInst

namespace DGInst

/-- **Satisfaction transfer along a comorphism into `DGInst`**, read with `DGSen.holds`. -/
theorem coHom_holds_iff {A : Inst.{u, v, 0, 0, 0}} (c : Inst.CoHom A DGInst) (S : A.Sign)
    (δ : DStrategy (c.Φ.obj S).E (c.Φ.obj S).F) (φ : (A.I.obj S).Sen) :
    DGSen.holds (E := (c.Φ.obj S).E) (F := (c.Φ.obj S).F) ((c.ρ.app S).sen φ) δ ↔
      (A.I.obj S).Sat ((c.ρ.app S).mod.obj δ) φ :=
  c.satisfaction S δ φ

end DGInst

/-! ## Functors out of discrete model categories -/

/-- A functor out of the discrete model category of a game is determined by its objects. -/
theorem Game.DModel.functor_ext {G : Game.{u}} {C : Type v} [Category.{w} C]
    {F F' : G.DModel ⥤ C} (h : ∀ σ, F.obj σ = F'.obj σ) : F = F' := by
  refine Functor.ext h ?_
  rintro σ _ ⟨rfl⟩
  have e : (⟨rfl⟩ : σ ⟶ σ) = 𝟙 σ := rfl
  rw [e, F.map_id, F'.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- A functor out of the discrete category of divergence-observing models is determined by its
objects. -/
theorem Game.DDModel.functor_ext {G : Game.{0}} {C : Type v} [Category.{w} C]
    {F F' : G.DDModel ⥤ C} (h : ∀ δ, F.obj δ = F'.obj δ) : F = F' := by
  refine Functor.ext h ?_
  rintro δ _ ⟨rfl⟩
  have e : (⟨rfl⟩ : δ ⟶ δ) = 𝟙 δ := rfl
  rw [e, F.map_id, F'.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

/-! ## Builders: comorphisms from a game reading -/

namespace GInst

/-- **A game reading** of an institution `A` with discrete-enough models: a game for each
signature, naturally, and a reading of each strategy of that game as an `A`-model, natural in
the signature (the reduct of a read model is the model read off the reduct). -/
structure Reading (A : Inst.{u, v, 0, 0, 0}) where
  /-- The game of each signature. -/
  game : A.Sign ⥤ Game.{0}
  /-- The `A`-model read off a strategy. -/
  mod : ∀ S : A.Sign, (game.obj S).Model → (A.I.obj S).Mod
  /-- Reading commutes with the reducts. -/
  mod_reduct : ∀ {S T : A.Sign} (f : S ⟶ T) (σ : (game.obj T).Model),
    (A.I.map f).mod.obj (mod T σ) = mod S (Game.reduct (game.map f) σ)

namespace Reading

variable {A : Inst.{u, v, 0, 0, 0}} (r : Reading A)

/-- The sentence translation of a reading: `φ` holds of `σ` when the model read off `σ`
satisfies it. -/
def sen (S : A.Sign) (φ : (A.I.obj S).Sen) : GSen (r.game.obj S).E (r.game.obj S).F :=
  ⟨fun σ => (A.I.obj S).Sat (r.mod S σ) φ⟩

/-- The model translation of a reading, as a functor out of the discrete model category. -/
def modFunctor (S : A.Sign) : (r.game.obj S).DModel ⥤ (A.I.obj S).Mod where
  obj := r.mod S
  map h := eqToHom (congrArg (r.mod S) h.down)
  map_id _ := eqToHom_refl _ _
  map_comp _ _ := (eqToHom_trans _ _).symm

/-- The corridor of a reading at a signature. -/
def corridor (S : A.Sign) : A.I.obj S ⟶ GInst.I.obj (r.game.obj S) :=
  ⟨r.sen S, r.modFunctor S, fun _ _ => Iff.rfl⟩

theorem sen_map {S T : A.Sign} (f : S ⟶ T) (φ : (A.I.obj S).Sen) :
    r.sen T ((A.I.map f).sen φ) = Game.senMap (r.game.map f) (r.sen S φ) :=
  GSen.ext (funext fun σ => propext <| ((A.I.map f).sat (r.mod T σ) φ).trans
    (iff_of_eq (congrArg (fun M => (A.I.obj S).Sat M φ) (r.mod_reduct f σ))))

theorem modFunctor_map {S T : A.Sign} (f : S ⟶ T) :
    r.modFunctor T ⋙ (A.I.map f).mod = Game.reductD (r.game.map f) ⋙ r.modFunctor S :=
  Game.DModel.functor_ext (r.mod_reduct f)

/-- **The comorphism of a game reading.** -/
def coHom : Inst.CoHom A GInst where
  Φ := r.game
  ρ :=
    { app := r.corridor
      naturality := fun _ _ f => Room.hom_ext (funext (r.sen_map f)) (r.modFunctor_map f) }

@[simp] theorem coHom_Φ : r.coHom.Φ = r.game := rfl

@[simp] theorem coHom_sen (S : A.Sign) (φ : (A.I.obj S).Sen) :
    (r.coHom.ρ.app S).sen φ = r.sen S φ := rfl

@[simp] theorem coHom_mod_obj (S : A.Sign) (σ : (r.game.obj S).Model) :
    (r.coHom.ρ.app S).mod.obj σ = r.mod S σ := rfl

@[simp] theorem holds_sen (S : A.Sign) (φ : (A.I.obj S).Sen) (σ : (r.game.obj S).Model) :
    (r.sen S φ).holds σ ↔ (A.I.obj S).Sat (r.mod S σ) φ := Iff.rfl

/-- A reading whose model maps are surjective gives a model-expansive comorphism. -/
theorem modelExpansive (h : ∀ S, Function.Surjective (r.mod S)) : r.coHom.ModelExpansive :=
  fun S => h S

/-- **Borrowing along a surjective reading**: entailment in `A` is entailment of the game
properties in `GInst`. -/
theorem entails_iff (h : ∀ S, Function.Surjective (r.mod S)) (S : A.Sign)
    (Γ : Set (A.I.obj S).Sen) (φ : (A.I.obj S).Sen) :
    (A.I.obj S).Entails Γ φ ↔ (GInst.I.obj (r.game.obj S)).Entails (r.sen S '' Γ) (r.sen S φ) :=
  r.coHom.entails_iff (r.modelExpansive h) S Γ φ

/-- **Precomposing a reading with a comorphism** `c : B → A`: the game of `S` is that of `c.Φ S`,
and the `B`-model read off a strategy is the `c`-translation of the `A`-model. -/
def precomp {B : Inst.{u', v', 0, 0, 0}} (c : Inst.CoHom B A) : Reading B where
  game := c.Φ ⋙ r.game
  mod S σ := (c.ρ.app S).mod.obj (r.mod (c.Φ.obj S) σ)
  mod_reduct {_ T} f σ := by
    have h := congrArg (fun k => k.mod.obj (r.mod (c.Φ.obj T) σ)) (c.ρ.naturality f)
    simp only [Room.comp_mod, Functor.comp_obj, Functor.comp_map] at h
    rw [h, r.mod_reduct]
    rfl

theorem precomp_sen {B : Inst.{u', v', 0, 0, 0}} (c : Inst.CoHom B A) (S : B.Sign)
    (φ : (B.I.obj S).Sen) : (r.precomp c).sen S φ = r.sen (c.Φ.obj S) ((c.ρ.app S).sen φ) :=
  GSen.ext (funext fun _ => propext ((c.ρ.app S).sat _ φ).symm)

/-- **Precomposing a reading is composing its comorphism**: `(r.precomp c).coHom` is
`c.comp r.coHom`. -/
theorem precomp_coHom {B : Inst.{u', v', 0, 0, 0}} (c : Inst.CoHom B A) :
    (r.precomp c).coHom = c.comp r.coHom := by
  refine Inst.CoHom.ext rfl ?_
  ext S : 2
  exact Room.hom_ext (funext (r.precomp_sen c S)) (Game.DModel.functor_ext fun _ => rfl)

end Reading

end GInst

namespace DGInst

/-- **A divergence-observing game reading** of an institution `A`: as `GInst.Reading`, with
divergence-observing strategies. -/
structure Reading (A : Inst.{u, v, 0, 0, 0}) where
  /-- The game of each signature. -/
  game : A.Sign ⥤ Game.{0}
  /-- The `A`-model read off a divergence-observing strategy. -/
  mod : ∀ S : A.Sign, DStrategy (game.obj S).E (game.obj S).F → (A.I.obj S).Mod
  /-- Reading commutes with the reducts. -/
  mod_reduct : ∀ {S T : A.Sign} (f : S ⟶ T) (δ : DStrategy (game.obj T).E (game.obj T).F),
    (A.I.map f).mod.obj (mod T δ) = mod S (DStrategy.reduct (game.map f) δ)

namespace Reading

variable {A : Inst.{u, v, 0, 0, 0}} (r : Reading A)

/-- The sentence translation of a reading. -/
def sen (S : A.Sign) (φ : (A.I.obj S).Sen) : DGSen (r.game.obj S).E (r.game.obj S).F :=
  ⟨fun δ => (A.I.obj S).Sat (r.mod S δ) φ⟩

/-- The model translation of a reading, as a functor out of the discrete model category. -/
def modFunctor (S : A.Sign) : (r.game.obj S).DDModel ⥤ (A.I.obj S).Mod where
  obj := r.mod S
  map h := eqToHom (congrArg (r.mod S) h.down)
  map_id _ := eqToHom_refl _ _
  map_comp _ _ := (eqToHom_trans _ _).symm

/-- The corridor of a reading at a signature. -/
def corridor (S : A.Sign) : A.I.obj S ⟶ DGInst.I.obj (r.game.obj S) :=
  ⟨r.sen S, r.modFunctor S, fun _ _ => Iff.rfl⟩

theorem sen_map {S T : A.Sign} (f : S ⟶ T) (φ : (A.I.obj S).Sen) :
    r.sen T ((A.I.map f).sen φ) = Game.dsenMap (r.game.map f) (r.sen S φ) :=
  DGSen.ext (funext fun δ => propext <| ((A.I.map f).sat (r.mod T δ) φ).trans
    (iff_of_eq (congrArg (fun M => (A.I.obj S).Sat M φ) (r.mod_reduct f δ))))

theorem modFunctor_map {S T : A.Sign} (f : S ⟶ T) :
    r.modFunctor T ⋙ (A.I.map f).mod = Game.dreductD (r.game.map f) ⋙ r.modFunctor S :=
  Game.DDModel.functor_ext (r.mod_reduct f)

/-- **The comorphism of a divergence-observing game reading.** -/
def coHom : Inst.CoHom A DGInst where
  Φ := r.game
  ρ :=
    { app := r.corridor
      naturality := fun _ _ f => Room.hom_ext (funext (r.sen_map f)) (r.modFunctor_map f) }

@[simp] theorem coHom_Φ : r.coHom.Φ = r.game := rfl

@[simp] theorem coHom_sen (S : A.Sign) (φ : (A.I.obj S).Sen) :
    (r.coHom.ρ.app S).sen φ = r.sen S φ := rfl

@[simp] theorem coHom_mod_obj (S : A.Sign) (δ : DStrategy (r.game.obj S).E (r.game.obj S).F) :
    (r.coHom.ρ.app S).mod.obj δ = r.mod S δ := rfl

@[simp] theorem holds_sen (S : A.Sign) (φ : (A.I.obj S).Sen)
    (δ : DStrategy (r.game.obj S).E (r.game.obj S).F) :
    (r.sen S φ).holds δ ↔ (A.I.obj S).Sat (r.mod S δ) φ := Iff.rfl

/-- A reading whose model maps are surjective gives a model-expansive comorphism. -/
theorem modelExpansive (h : ∀ S, Function.Surjective (r.mod S)) : r.coHom.ModelExpansive :=
  fun S => h S

/-- A `GInst` reading followed by `GInst.toDGInst` is the reading of the finite plays. -/
def ofGInst (r : GInst.Reading A) : Reading A where
  game := r.game
  mod S δ := r.mod S δ.toStrategy
  mod_reduct f δ := r.mod_reduct f δ.toStrategy

end Reading

end DGInst

end Silmaril.Games
