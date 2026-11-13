module

public import Silmaril.Games.Handler.Thms
public import Mathlib.CategoryTheory.Category.Preorder
public import Silmaril.Logic.Institution.Morphism

/-!
# The institution of game semantics

`GInst : Inst.{1, 0, 0, 0, 0}` is the institution whose signatures are games, whose models are
strategies and whose sentences are properties of strategies. It is the common target of the
game readings of the Wasm logics (`Silmaril.Wasm.Institution.GameInst`) and of non-Wasm systems
(`Silmaril.Games.Examples.Counter`). The design is `docs/projects/spectec/README.md` §2.

* **Signatures** `Game`: a pair `(E, F)` of effect signatures, the lower interface `E` (calls
  made) and the upper interface `F` (calls served).
* **Signature morphisms** `(E, F) ⟶ (E', F')`: pairs `lo : Sig.Hom E' E`, `up : Sig.Hom F F'`.
  They are contravariant below and covariant above, like lenses, so that a component of the
  larger game can be read as a component of the smaller one.
* **Models** at `(E, F)`: strategies `Strategy E F`. In `GInst` model morphisms are equalities
  (`Game.DModel`), as in every institution of the Wasm graph. Discrete institutions map into
  `GInst` by comorphisms only if its models are discrete too, because the model translation
  goes from `GInst` back to the source. `GInstRef` has refinement `σ ≤ τ` as (thin) model
  morphisms, and the identity comorphism `GInstRef.toGInst` relates the two.
* **Reduct** along `f`: `reduct f σ' = (ofHandler (ofHom f.lo)).comp (σ'.restrict f.up)`. It
  hides the upper operations outside the image of `f.up` and forwards every lower call `m'`
  of `σ'` to `f.lo.op m'`. It is strictly functorial (`reduct_id`, `reduct_comp`), monotone
  (`reduct_mono`) and preserves nonempty joins (`reduct_sSup`).
* **Sentences** `GSen E F`: properties of strategies. The play sentences `box S`
  (safety: every play lies in `S`), `dia T` (some play lies in `T`; `diaPlay s` is the test
  witness `s`), `and` and `top` are smart constructors. Translation precomposes with the
  reduct.
* **Satisfaction**: `σ ⊨ φ` iff `φ.holds σ`.

## Why sentences are semantic

Sentence translation must be strictly functorial. An inductive syntax with `box S`
translated to `box (pull f S)` is not: `pull (𝟙 _) S` is the set of plays `s` all of whose
induced plays lie in `S`, which differs from `S` on plays that are not legal. So sentences are
predicates on strategies, and the play constructors form a fragment that is *closed under
translation*: `map_box : (box S).map f = box (pull f S)` and
`map_dia : (dia T).map f = dia (push f T)` (`Silmaril.Games.Institution.Thms`). Here
`pull`/`push` are preimages along the relation "`p` is a play of the reduct of the principal
strategy of `s`". This relation is the move map of the design, and the theorem behind it
(`mem_reduct_iff`) says that **the plays of the reduct are the image of the plays of `σ'`**.
It follows from the preservation of joins, so it needs no description of the copycat
forwarding.

The satisfaction condition of `GInst` therefore holds by definition. Its content is in
`mem_reduct_iff` and in the fragment lemmas.
-/

@[expose] public section

namespace Silmaril.Games

open CategoryTheory Silmaril.Logic.Institution

universe u

/-- A game `E ↠ F`: the lower interface `E` (calls made) and the upper interface `F` (calls
served). -/
structure Game : Type (u + 1) where
  /-- The lower interface. -/
  E : Sig.{u}
  /-- The upper interface. -/
  F : Sig.{u}

namespace Game

/-- A morphism of games `G ⟶ G'`: the lower interface of `G'` renamed into that of `G`, and
the upper interface of `G` renamed into that of `G'`. -/
structure Hom (G G' : Game.{u}) : Type u where
  /-- Lower renaming (contravariant). -/
  lo : Sig.Hom G'.E G.E
  /-- Upper renaming (covariant). -/
  up : Sig.Hom G.F G'.F

/-- Games and their morphisms form a category. -/
instance category : Category.{u} Game.{u} where
  Hom := Hom
  id G := ⟨Sig.Hom.id G.E, Sig.Hom.id G.F⟩
  comp f g := ⟨g.lo.comp f.lo, f.up.comp g.up⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_lo (G : Game.{u}) : (𝟙 G : Hom G G).lo = Sig.Hom.id G.E := rfl
@[simp] theorem id_up (G : Game.{u}) : (𝟙 G : Hom G G).up = Sig.Hom.id G.F := rfl
@[simp] theorem comp_lo {G G' G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') :
    (f ≫ g : Hom G G'').lo = g.lo.comp f.lo := rfl
@[simp] theorem comp_up {G G' G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') :
    (f ≫ g : Hom G G'').up = f.up.comp g.up := rfl

/-- The models of a game: its strategies. -/
abbrev Model (G : Game.{u}) : Type u := Strategy G.E G.F

/-- The reduct of a strategy along a game morphism: hide the upper operations outside the
image of `f.up` and forward lower calls along `f.lo`. -/
def reduct {G G' : Game.{u}} (f : G ⟶ G') (σ : G'.Model) : G.Model :=
  (Strategy.ofHandler (Handler.ofHom f.lo)).comp (σ.restrict f.up)

/-- The reduct along the identity is the identity. -/
theorem reduct_id (G : Game.{u}) (σ : G.Model) : reduct (𝟙 G) σ = σ := by
  change (Strategy.ofHandler (Handler.ofHom (Sig.Hom.id G.E))).comp
    (σ.restrict (Sig.Hom.id G.F)) = σ
  rw [Strategy.restrict_id, show Handler.ofHom (Sig.Hom.id G.E) = Handler.id G.E from rfl,
    Strategy.ofHandler_id, Strategy.id_comp]

/-- Forwarding along a composite renaming is the composite of the forwardings. -/
theorem ofHandler_ofHom_comp {E E' E'' : Sig.{u}} (g : Sig.Hom E'' E') (f : Sig.Hom E' E) :
    Strategy.ofHandler (Handler.ofHom (g.comp f)) =
      (Strategy.ofHandler (Handler.ofHom f)).comp (Strategy.ofHandler (Handler.ofHom g)) := by
  rw [← Strategy.ofHandler_comp]
  rfl

/-- The reduct along a composite is the composite of the reducts. -/
theorem reduct_comp {G G' G'' : Game.{u}} (f : G ⟶ G') (g : G' ⟶ G'') (σ : G''.Model) :
    reduct (f ≫ g) σ = reduct f (reduct g σ) := by
  change (Strategy.ofHandler (Handler.ofHom (g.lo.comp f.lo))).comp
    (σ.restrict (f.up.comp g.up)) = _
  rw [ofHandler_ofHom_comp, Strategy.restrict_comp]
  simp only [reduct, Strategy.restrict, Strategy.comp_assoc]

/-- The reduct is monotone. -/
theorem reduct_mono {G G' : Game.{u}} (f : G ⟶ G') : Monotone (reduct f) := fun _ _ h =>
  Strategy.comp_mono_right _ (Strategy.restrict_mono h _)

/-- The reduct preserves nonempty joins. -/
theorem reduct_sSup {G G' : Game.{u}} (f : G ⟶ G') {S : Set G'.Model} (hS : S.Nonempty) :
    reduct f (sSup S) = sSup (reduct f '' S) := by
  rw [reduct, Strategy.restrict, Strategy.comp_sSup_left hS,
    Strategy.comp_sSup_right _ (hS.image _), Set.image_image]
  rfl

end Game

/-! ## Principal strategies and maps preserving joins -/

namespace Strategy

variable {E F E' F' : Sig.{u}}

/-- The principal strategy of a play: the least strategy containing it (if it is legal). -/
def principal (s : List (Move E F)) : Strategy E F := generate {s}

/-- A play of `σ` generates a strategy below `σ`. -/
theorem principal_le {σ : Strategy E F} {s : List (Move E F)} (hs : s ∈ σ) :
    principal s ≤ σ :=
  generate_le fun _ ht _ => (Set.mem_singleton_iff.1 ht) ▸ hs

/-- A legal play belongs to its principal strategy. -/
theorem mem_principal_self {s : List (Move E F)} (hl : Legal s) : s ∈ principal s :=
  subset_generate rfl hl

/-- Every strategy is the join of the principal strategies of its plays. -/
theorem eq_sSup_principal (σ : Strategy E F) : σ = sSup (principal '' σ.plays) := by
  have hne : (principal '' σ.plays).Nonempty := ⟨_, [], σ.nil_mem, rfl⟩
  apply le_antisymm
  · intro s hs
    exact (mem_sSup_of_nonempty hne).2 ⟨_, ⟨s, hs, rfl⟩, mem_principal_self (σ.legal hs)⟩
  · exact sSup_le (by rintro _ ⟨s, hs, rfl⟩; exact principal_le hs)

/-- A map of strategies preserving nonempty joins is determined by its values on principal
strategies: the plays of `R σ` are those of `R (principal s)` for the plays `s` of `σ`. -/
theorem mem_of_sSup {R : Strategy E' F' → Strategy E F}
    (hR : ∀ S : Set (Strategy E' F'), S.Nonempty → R (sSup S) = sSup (R '' S))
    (σ : Strategy E' F') (p : List (Move E F)) :
    p ∈ R σ ↔ ∃ s ∈ σ, p ∈ R (principal s) := by
  have hne : (principal '' σ.plays).Nonempty := ⟨_, [], σ.nil_mem, rfl⟩
  conv_lhs => rw [eq_sSup_principal σ, hR _ hne]
  rw [mem_sSup_of_nonempty (hne.image R)]
  constructor
  · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hp⟩
    exact ⟨s, hs, hp⟩
  · rintro ⟨s, hs, hp⟩
    exact ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hp⟩

end Strategy

namespace Game

variable {G G' : Game.{u}}

/-- **The plays of a reduct are the image of the plays of the model** under the relation
"`p` is a play of the reduct of the principal strategy of `s`". -/
theorem mem_reduct_iff (f : G ⟶ G') (σ : G'.Model) (p : List (Move G.E G.F)) :
    p ∈ reduct f σ ↔ ∃ s ∈ σ, p ∈ reduct f (Strategy.principal s) :=
  Strategy.mem_of_sSup (fun _ hS => reduct_sSup f hS) σ p

end Game

/-! ## The upper half: how restriction renames moves -/

/-- How a move of `σ : Strategy X F` is seen in `σ.restrict ρ`, for `ρ : Sig.Hom G F`: lower
moves are unchanged, a question `ρ.op q` is seen as `q`, and an answer `n` to `ρ.op q` is
seen as `ρ.ar q n`. Lifted to plays with `List.Forall₂`, it is the move map of the upper
half of the reduct (`Strategy.restrict_sound`). -/
inductive UpRel {X G F : Sig.{u}} (ρ : Sig.Hom G F) : Move X F → Move X G → Prop
  /-- A lower move is unchanged. -/
  | low (e : Ev X) : UpRel ρ (.inl e) (.inl e)
  /-- The question `ρ.op q` is seen as `q`. -/
  | ask (q : G.Op) : UpRel ρ (.inr (.ask (ρ.op q))) (.inr (.ask q))
  /-- The answer `n` to `ρ.op q` is seen as `ρ.ar q n`. -/
  | ans (q : G.Op) (n : F.Ar (ρ.op q)) :
      UpRel ρ (.inr (.ans (ρ.op q) n)) (.inr (.ans q (ρ.ar q n)))

/-! ## Sentences -/

/-- A sentence about strategies of `E ↠ F`: a property of strategies. The play sentences
`box`, `dia`, `and`, `top` below are the syntactic fragment. -/
@[ext] structure GSen (E F : Sig.{u}) : Type u where
  /-- The strategies satisfying the sentence. -/
  holds : Strategy E F → Prop

namespace GSen

variable {E F : Sig.{u}}

/-- `□ S`, safety: every play lies in `S`. -/
def box (S : Set (List (Move E F))) : GSen E F := ⟨fun σ => ∀ s ∈ σ, s ∈ S⟩

/-- `◇ T`: some play lies in `T`. -/
def dia (T : Set (List (Move E F))) : GSen E F := ⟨fun σ => ∃ s ∈ T, s ∈ σ⟩

/-- `◇ s`, a test witness: the play `s` is possible. -/
def diaPlay (s : List (Move E F)) : GSen E F := dia {s}

/-- Conjunction. -/
protected def and (φ ψ : GSen E F) : GSen E F := ⟨fun σ => φ.holds σ ∧ ψ.holds σ⟩

/-- Truth. -/
protected def top : GSen E F := ⟨fun _ => True⟩

@[inherit_doc] scoped prefix:100 "□ " => GSen.box
@[inherit_doc] scoped prefix:100 "◇ " => GSen.dia

/-- `σ` satisfies `□ S` iff all its plays lie in `S`. -/
@[simp] theorem holds_box {S : Set (List (Move E F))} {σ : Strategy E F} :
    (box S).holds σ ↔ ∀ s ∈ σ, s ∈ S := Iff.rfl

/-- `σ` satisfies `◇ T` iff one of its plays lies in `T`. -/
@[simp] theorem holds_dia {T : Set (List (Move E F))} {σ : Strategy E F} :
    (dia T).holds σ ↔ ∃ s ∈ T, s ∈ σ := Iff.rfl

/-- `σ` satisfies `◇ s` iff `s` is a play of `σ`. -/
@[simp] theorem holds_diaPlay {s : List (Move E F)} {σ : Strategy E F} :
    (diaPlay s).holds σ ↔ s ∈ σ := by
  simp [diaPlay]

/-- A universal sentence: satisfaction goes down refinement. -/
def Universal (φ : GSen E F) : Prop := ∀ ⦃σ τ : Strategy E F⦄, σ ≤ τ → φ.holds τ → φ.holds σ

/-- An existential sentence: satisfaction goes up refinement. -/
def Existential (φ : GSen E F) : Prop :=
  ∀ ⦃σ τ : Strategy E F⦄, σ ≤ τ → φ.holds σ → φ.holds τ

end GSen

namespace Game

variable {G G' : Game.{u}}

/-- Sentence translation along a game morphism: evaluate on the reduct. -/
def senMap (f : G ⟶ G') (φ : GSen G.E G.F) : GSen G'.E G'.F :=
  ⟨fun σ' => φ.holds (reduct f σ')⟩

/-- Preimage of a set of plays along `f`: the plays `s` all of whose induced plays lie in
`S`. -/
def pull (f : G ⟶ G') (S : Set (List (Move G.E G.F))) : Set (List (Move G'.E G'.F)) :=
  {s | ∀ p ∈ reduct f (Strategy.principal s), p ∈ S}

/-- Existential preimage of a set of plays along `f`: the plays `s` inducing a play in `T`. -/
def push (f : G ⟶ G') (T : Set (List (Move G.E G.F))) : Set (List (Move G'.E G'.F)) :=
  {s | ∃ p ∈ T, p ∈ reduct f (Strategy.principal s)}

/-- The reduct as a functor between the thin categories of models. -/
def reductFunctor (f : G ⟶ G') : G'.Model ⥤ G.Model := (reduct_mono f).functor

/-- Models of a game with equalities as model morphisms (a discrete category). This is the
model category of `GInst`, as in the other institutions of the Wasm graph. -/
def DModel (G : Game.{u}) : Type u := G.Model

/-- The discrete category of models (homs are equalities, wrapped in `PLift`). -/
instance DModel.category (G : Game.{u}) : Category.{0} G.DModel where
  Hom σ τ := PLift (σ = τ)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- The reduct as a functor between the discrete categories of models. -/
def reductD (f : G ⟶ G') : G'.DModel ⥤ G.DModel where
  obj σ := reduct f σ
  map h := ⟨congrArg (reduct f) h.down⟩

/-- A discrete model is a thin one. -/
def DModel.toModel (G : Game.{u}) : G.DModel ⥤ G.Model where
  obj σ := (σ : G.Model)
  map h := homOfLE (le_of_eq h.down)

end Game

/-! ## The institution -/

namespace GInst

open Game

/-- The room of a game: play sentences, strategies, satisfaction. -/
def room (G : Game.{0}) : Room.{0, 0, 0} :=
  ⟨GSen G.E G.F, Cat.of G.DModel, fun σ φ => φ.holds σ⟩

/-- The corridor of a game morphism. The satisfaction condition holds by definition of
sentence translation; see the module documentation. -/
def corridor {G G' : Game.{0}} (f : G ⟶ G') : room G ⟶ room G' :=
  ⟨senMap f, reductD f, fun _ _ => Iff.rfl⟩

theorem senMap_id (G : Game.{0}) : senMap (𝟙 G) = id :=
  funext fun φ => GSen.ext (funext fun σ => by
    change φ.holds (reduct (𝟙 G) σ) = φ.holds σ
    rw [reduct_id])

theorem senMap_comp {G G' G'' : Game.{0}} (f : G ⟶ G') (g : G' ⟶ G'') :
    senMap (f ≫ g) = senMap g ∘ senMap f :=
  funext fun φ => GSen.ext (funext fun σ => by
    change φ.holds (reduct (f ≫ g) σ) = φ.holds (reduct f (reduct g σ))
    rw [reduct_comp])

/-- The institution of game semantics, as a functor into rooms. -/
def institution : Game.{0} ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id G := Room.hom_ext (senMap_id G) (Functor.ext (fun σ => reduct_id G σ) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (senMap_comp f g)
    (Functor.ext (fun σ => reduct_comp f g σ) (fun _ _ _ => rfl))

/-- The room of a game with refinement as model morphisms. -/
def roomRef (G : Game.{0}) : Room.{0, 0, 0} :=
  ⟨GSen G.E G.F, Cat.of G.Model, fun σ φ => φ.holds σ⟩

/-- The corridor of a game morphism, with refinement as model morphisms. -/
def corridorRef {G G' : Game.{0}} (f : G ⟶ G') : roomRef G ⟶ roomRef G' :=
  ⟨senMap f, reductFunctor f, fun _ _ => Iff.rfl⟩

/-- The institution of game semantics with refinement as model morphisms. -/
def institutionRef : Game.{0} ⥤ Room.{0, 0, 0} where
  obj := roomRef
  map := corridorRef
  map_id G := Room.hom_ext (senMap_id G) (Functor.ext (fun σ => reduct_id G σ) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (senMap_comp f g)
    (Functor.ext (fun σ => reduct_comp f g σ) (fun _ _ _ => rfl))

end GInst

/-- **The institution of game semantics** `GInst`: games, strategies, and properties of
strategies, with reducts along lens-like game morphisms. Model morphisms are equalities, as in
the rest of the Wasm graph, so that discrete institutions map into it by comorphisms. -/
def GInst : Inst.{1, 0, 0, 0, 0} := ⟨Game.{0}, GInst.institution⟩

/-- `GInst` with refinement `σ ≤ τ` as model morphisms. -/
def GInstRef : Inst.{1, 0, 0, 0, 0} := ⟨Game.{0}, GInst.institutionRef⟩

/-- The identity comorphism `GInstRef → GInst`: sentences are unchanged, and a model is read
as a refinement-ordered one. -/
def GInstRef.toGInst : Inst.CoHom GInstRef GInst where
  Φ := 𝟭 _
  ρ :=
    { app := fun G => ⟨id, Game.DModel.toModel G, fun _ _ => Iff.rfl⟩
      naturality := fun _ _ _ =>
        Room.hom_ext rfl (Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

end Silmaril.Games
