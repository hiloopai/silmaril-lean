module

public import Silmaril.Encoding.Per
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Categories of encodings

* `EncCat σ`: objects are encodings `(α, E : EncRel σ α)` with a fixed carrier
  `σ`; a morphism `(α, E) ⟶ (β, F)` is a function `f : α → β` that preserves
  spellings (`E s a → F s (f a)`, i.e. `E ≤ comap f F`).
* `EncCat₂`: objects `(σ, α, E)` with varying carrier; a morphism is a pair
  `(g : σ → σ', f : α → β)` with `E s a → F (g s) (f a)`.
* `EncCat.incl σ : EncCat σ ⥤ EncCat₂` (written `ι σ` in the docs) sends `f` to
  `(id, f)`.  It is faithful, injective on objects, and its object image is
  exactly the carrier-`σ` objects (`incl_obj_surj`).
* **`EncCat.isoCarrierFiber σ`**: `EncCat σ` is isomorphic, in `Cat`, to
  Mathlib's fiber `EncCat₂.carrierFunctor.Fiber σ`, whose objects are
  `{X : EncCat₂ // X.carrier = σ}` and whose morphisms are the `EncCat₂`
  morphisms lying over `𝟙 σ` (`IsHomLift`).  The object maps are mutually
  inverse casts.  The older presentation `Fixed σ` (Mathlib's
  `InducedWideCategory` over the image of `incl σ`, with morphism property
  `IdOnCarrier`) is kept as `isoFixed`; there the object half is definitionally
  the identity and the content is `idOnCarrier_iff_mem_range`.
* The fiber of `EncCat.forget σ` over `α` is equivalent to the lattice
  `EncRel σ α` viewed as a thin category (`forgetFiberEquiv`): the functor
  `toForgetFiber` is fully faithful and bijective on objects
  (`toForgetFiber_obj_bijective`).  (An isomorphism in `Cat` would need a
  `ULift`, since `EncRel σ α : Type` while the fiber lives in `Type 1`.)
* Carrier change: `pushFunctor g ⊣ pullFunctor g`, and the `(g, id)` morphisms
  form natural transformations `incl σ ⟶ pushFunctor g ⋙ incl σ'` and
  `pullFunctor g ⋙ incl σ ⟶ incl σ'`, which are respectively cocartesian and
  cartesian over `carrierFunctor`: every morphism out of (into) an included
  object factors uniquely through them (`factor_through_push`,
  `factor_through_pull`).
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

/-- An object of `EncCat σ`: abstract syntax together with its encoding in the
carrier `σ`. -/
structure EncCat (σ : Type) : Type 1 where
  /-- The abstract syntax. -/
  ast : Type
  /-- The encoding relation. -/
  rel : EncRel σ ast

namespace EncCat

variable {σ σ' : Type}

/-- Encoding-preserving functions. -/
@[ext]
structure Hom (X Y : EncCat σ) where
  /-- The underlying function on abstract syntax. -/
  fn : X.ast → Y.ast
  /-- Every spelling of `a` is a spelling of `fn a`. -/
  preserves : EncRel.Preserves X.rel Y.rel fn

instance category : Category (EncCat σ) where
  Hom := Hom
  id _ := ⟨id, fun _ _ h => h⟩
  comp f g := ⟨g.fn ∘ f.fn, fun _ _ h => g.preserves _ _ (f.preserves _ _ h)⟩

/-- The object `(α, E)`. -/
abbrev of (α : Type) (E : EncRel σ α) : EncCat σ := ⟨α, E⟩

@[ext] theorem hom_ext {X Y : EncCat σ} {f g : X ⟶ Y} (h : f.fn = g.fn) : f = g :=
  Hom.ext h

@[simp] theorem id_fn (X : EncCat σ) : (𝟙 X : X ⟶ X).fn = id := rfl

@[simp] theorem comp_fn {X Y Z : EncCat σ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fn = g.fn ∘ f.fn := rfl

/-- Build a morphism from a spelling-preserving function. -/
def homMk {X Y : EncCat σ} (f : X.ast → Y.ast) (h : EncRel.Preserves X.rel Y.rel f) :
    X ⟶ Y := ⟨f, h⟩

theorem nonempty_hom_iff {X Y : EncCat σ} (f : X.ast → Y.ast) :
    (∃ h : X ⟶ Y, h.fn = f) ↔ X.rel ≤ EncRel.comap f Y.rel :=
  ⟨fun ⟨h, hf⟩ => hf ▸ h.preserves, fun h => ⟨⟨f, h⟩, rfl⟩⟩

/-- Morphisms preserve the induced PER on the carrier. -/
theorem Hom.per {X Y : EncCat σ} (f : X ⟶ Y) {s s' : σ} (h : X.rel.per s s') :
    Y.rel.per s s' :=
  EncRel.Preserves.per f.preserves h

theorem Hom.same {X Y : EncCat σ} (f : X ⟶ Y) {s s' : σ} (h : X.rel.same s s') :
    Y.rel.same s s' :=
  EncRel.Preserves.same f.preserves h

/-! ## The forgetful functor and the fibers -/

/-- Forget the encoding. -/
@[simps]
def forget (σ : Type) : EncCat σ ⥤ Type where
  obj X := X.ast
  map f := TypeCat.ofHom f.fn

instance : (forget σ).Faithful where
  map_injective {X Y} f g h := by
    ext a
    exact congrArg (fun k : X.ast ⟶ Y.ast => k a) h

/-- `id` is a morphism `(α, E) ⟶ (α, F)` exactly when `E ≤ F`. -/
theorem le_iff_exists_hom_id {α : Type} {E F : EncRel σ α} :
    E ≤ F ↔ ∃ f : of α E ⟶ of α F, f.fn = id :=
  (nonempty_hom_iff (X := of α E) (Y := of α F) id).symm

/-- The fiber over `α` is thin: there is at most one morphism over `id`. -/
theorem fiber_thin {α : Type} {E F : EncRel σ α} (f g : of α E ⟶ of α F)
    (hf : f.fn = id) (hg : g.fn = id) : f = g :=
  hom_ext (hf.trans hg.symm)

/-- The lattice `EncRel σ α`, as a thin category, includes into `EncCat σ`
over `α`.  Its corestriction to the fiber of `forget` is `toForgetFiber`. -/
@[simps]
def fiberInclusion (σ α : Type) : EncRel σ α ⥤ EncCat σ where
  obj E := of α E
  map h := ⟨id, fun s a hs => h.le s a hs⟩

instance (α : Type) : (fiberInclusion σ α).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- Every morphism over `id` in the fiber comes from the lattice order. -/
theorem fiberInclusion_full_over_id {α : Type} {E F : EncRel σ α}
    (f : of α E ⟶ of α F) (hf : f.fn = id) :
    ∃ h : E ⟶ F, (fiberInclusion σ α).map h = f :=
  ⟨homOfLE (le_iff_exists_hom_id.mpr ⟨f, hf⟩), fiber_thin _ _ rfl hf⟩

theorem fiberInclusion_comp_forget (α : Type) (E : EncRel σ α) :
    (forget σ).obj ((fiberInclusion σ α).obj E) = α := rfl

/-- `fiberInclusion σ α` lies over the constant functor at `α`. -/
theorem fiberInclusion_comp_forget_eq (α : Type) :
    fiberInclusion σ α ⋙ forget σ = (Functor.const (EncRel σ α)).obj α := rfl

/-- The lattice `EncRel σ α` as a functor into Mathlib's fiber of `forget σ`
over `α`. -/
def toForgetFiber (α : Type) : EncRel σ α ⥤ (forget σ).Fiber α :=
  Functor.Fiber.inducedFunctor (fiberInclusion_comp_forget_eq α)

@[simp] theorem toForgetFiber_obj_val (α : Type) (E : EncRel σ α) :
    ((toForgetFiber α).obj E).1 = of α E := rfl

/-- A morphism of the fiber of `forget σ` between objects with syntax `α` has
underlying function `id`. -/
theorem forgetFiber_fn_eq_id {α : Type} {E F : EncRel σ α}
    (φ : (toForgetFiber α).obj E ⟶ (toForgetFiber α).obj F) : φ.1.fn = id := by
  obtain ⟨φ, hφ⟩ := φ
  have h := IsHomLift.fac' (forget σ) (𝟙 α) φ
  simp only [Category.id_comp] at h
  funext a
  exact congrArg (fun k : α ⟶ α => k a) h

theorem toForgetFiber_obj_injective (α : Type) :
    Function.Injective (toForgetFiber (σ := σ) α).obj := by
  intro E F h
  have h' := congrArg (fun X : (forget σ).Fiber α => X.1) h
  change (of α E) = (of α F) at h'
  cases h'
  rfl

theorem toForgetFiber_obj_surjective (α : Type) :
    Function.Surjective (toForgetFiber (σ := σ) α).obj := by
  rintro ⟨⟨β, F⟩, h⟩
  change β = α at h
  subst h
  exact ⟨F, rfl⟩

/-- **The fiber of `forget σ` over `α` is the lattice `EncRel σ α`**, up to a
bijection on objects. -/
theorem toForgetFiber_obj_bijective (α : Type) :
    Function.Bijective (toForgetFiber (σ := σ) α).obj :=
  ⟨toForgetFiber_obj_injective α, toForgetFiber_obj_surjective α⟩

instance (α : Type) : (toForgetFiber (σ := σ) α).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance (α : Type) : (toForgetFiber (σ := σ) α).Full where
  map_surjective {E F} φ := by
    have hφ := forgetFiber_fn_eq_id φ
    refine ⟨homOfLE (le_iff_exists_hom_id.mpr ⟨φ.1, hφ⟩), ?_⟩
    apply Functor.Fiber.hom_ext
    exact hom_ext hφ.symm

instance (α : Type) : (toForgetFiber (σ := σ) α).EssSurj where
  mem_essImage Y := by
    obtain ⟨E, rfl⟩ := toForgetFiber_obj_surjective α Y
    exact ⟨E, ⟨Iso.refl _⟩⟩

instance (α : Type) : (toForgetFiber (σ := σ) α).IsEquivalence where

/-- The equivalence `EncRel σ α ≌ (forget σ).Fiber α`. -/
noncomputable def forgetFiberEquiv (α : Type) : EncRel σ α ≌ (forget σ).Fiber α :=
  (toForgetFiber α).asEquivalence

/-! ## Carrier change -/

/-- Pushforward of encodings along a carrier map `g` (`g_!`). -/
@[simps]
def pushFunctor (g : σ → σ') : EncCat σ ⥤ EncCat σ' where
  obj X := ⟨X.ast, X.rel.push g⟩
  map f := ⟨f.fn, by
    rintro s' a ⟨s, rfl, h⟩
    exact ⟨s, rfl, f.preserves _ _ h⟩⟩

/-- Pullback of encodings along a carrier map `g` (`g^*`). -/
@[simps]
def pullFunctor (g : σ → σ') : EncCat σ' ⥤ EncCat σ where
  obj X := ⟨X.ast, X.rel.pull g⟩
  map f := ⟨f.fn, fun _ _ h => f.preserves _ _ h⟩

/-- `g_! ⊣ g^*` on categories of encodings: both sides of the hom-set bijection
are the same functions, by the Galois connection `push g ⊣ pull g`. -/
def pushPullAdjunction (g : σ → σ') : pushFunctor g ⊣ pullFunctor g :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.fn, fun s a h => f.preserves (g s) a ⟨s, rfl, h⟩⟩
          invFun := fun f => ⟨f.fn, by
            rintro s' a ⟨s, rfl, h⟩
            exact f.preserves s a h⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } }

/-- Pullback along `id` is the identity functor. -/
theorem pullFunctor_id : pullFunctor (σ := σ) id = 𝟭 _ := rfl

/-- Pullback along an injective map undoes pushforward on objects. -/
theorem pullFunctor_obj_pushFunctor_obj {g : σ → σ'} (hg : Function.Injective g)
    (X : EncCat σ) : (pullFunctor g).obj ((pushFunctor g).obj X) = X := by
  change (⟨X.ast, (X.rel.push g).pull g⟩ : EncCat σ) = X
  rw [EncRel.pull_push_of_injective hg]

end EncCat

/-! ## Encodings with varying carrier -/

/-- An object of `EncCat₂`: a carrier, abstract syntax, and an encoding. -/
structure EncCat₂ : Type 1 where
  /-- The carrier (bytes, text, …). -/
  carrier : Type
  /-- The abstract syntax. -/
  ast : Type
  /-- The encoding relation. -/
  rel : EncRel carrier ast

namespace EncCat₂

/-- Morphisms: a carrier map and a syntax map jointly preserving spellings. -/
@[ext]
structure Hom (X Y : EncCat₂) where
  /-- The map on carriers. -/
  onCarrier : X.carrier → Y.carrier
  /-- The map on abstract syntax. -/
  fn : X.ast → Y.ast
  /-- A spelling `s` of `a` maps to a spelling `onCarrier s` of `fn a`. -/
  preserves : ∀ s a, X.rel s a → Y.rel (onCarrier s) (fn a)

instance category : Category EncCat₂ where
  Hom := Hom
  id _ := ⟨id, id, fun _ _ h => h⟩
  comp f g := ⟨g.onCarrier ∘ f.onCarrier, g.fn ∘ f.fn,
    fun _ _ h => g.preserves _ _ (f.preserves _ _ h)⟩

@[ext] theorem hom_ext {X Y : EncCat₂} {f g : X ⟶ Y} (h₁ : f.onCarrier = g.onCarrier)
    (h₂ : f.fn = g.fn) : f = g :=
  Hom.ext h₁ h₂

@[simp] theorem id_onCarrier (X : EncCat₂) : (𝟙 X : X ⟶ X).onCarrier = id := rfl
@[simp] theorem id_fn (X : EncCat₂) : (𝟙 X : X ⟶ X).fn = id := rfl
@[simp] theorem comp_onCarrier {X Y Z : EncCat₂} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).onCarrier = g.onCarrier ∘ f.onCarrier := rfl
@[simp] theorem comp_fn {X Y Z : EncCat₂} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fn = g.fn ∘ f.fn := rfl

/-- Morphisms map same-value spellings to same-value spellings. -/
theorem Hom.same {X Y : EncCat₂} (f : X ⟶ Y) {s s' : X.carrier} (h : X.rel.same s s') :
    Y.rel.same (f.onCarrier s) (f.onCarrier s') := by
  obtain ⟨a, h, h'⟩ := h
  exact ⟨f.fn a, f.preserves _ _ h, f.preserves _ _ h'⟩

theorem Hom.per {X Y : EncCat₂} (f : X ⟶ Y) {s s' : X.carrier} (h : X.rel.per s s') :
    Y.rel.per (f.onCarrier s) (f.onCarrier s') := by
  induction h with
  | single h => exact .single (f.same h)
  | tail _ h ih => exact .tail ih (f.same h)

/-- Forget to the carrier. -/
@[simps]
def carrierFunctor : EncCat₂ ⥤ Type where
  obj X := X.carrier
  map f := TypeCat.ofHom f.onCarrier

/-- Forget to the abstract syntax. -/
@[simps]
def astFunctor : EncCat₂ ⥤ Type where
  obj X := X.ast
  map f := TypeCat.ofHom f.fn

/-- A syntax map `f` together with "decode, apply `f`, re-encode" on carriers
is a morphism whenever the decoder is complete and the encoder is correct on
the image.  (`default` is the junk value used off the domain.) -/
def homOfCodec {X Y : EncCat₂} (f : X.ast → Y.ast) (dec : X.carrier → Option X.ast)
    (enc : Y.ast → Y.carrier) (default : Y.carrier) (hdec : X.rel.DecoderComplete dec)
    (henc : ∀ a, a ∈ X.rel.image → Y.rel (enc (f a)) (f a)) : X ⟶ Y where
  onCarrier s := (dec s).elim default (enc ∘ f)
  fn := f
  preserves s a h := by
    rw [hdec s a h]
    exact henc a ⟨s, h⟩

/-- Morphisms whose source and target carriers coincide and whose carrier map
is the identity (heterogeneously, since the carriers are only propositionally
equal).  The carrier equation is needed: without it the condition would hold
vacuously for every morphism out of an empty carrier. -/
def IdOnCarrier : MorphismProperty EncCat₂ := fun X Y f =>
  X.carrier = Y.carrier ∧ ∀ s, f.onCarrier s ≍ s

instance : IdOnCarrier.IsMultiplicative where
  id_mem _ := ⟨rfl, fun _ => HEq.rfl⟩
  comp_mem f _ hf hg := ⟨hf.1.trans hg.1, fun s => (hg.2 (f.onCarrier s)).trans (hf.2 s)⟩

/-- `IdOnCarrier` is not vacuous on empty carriers: no morphism between
objects with carriers `Empty` and `Bool` satisfies it. -/
theorem not_idOnCarrier_empty_bool {α β : Type} (E : EncRel Empty α) (F : EncRel Bool β)
    (f : (⟨Empty, α, E⟩ : EncCat₂) ⟶ ⟨Bool, β, F⟩) : ¬ IdOnCarrier f := by
  rintro ⟨h, -⟩
  have h' : (Empty : Type) = Bool := h
  exact Empty.elim (cast h'.symm true)

end EncCat₂

namespace EncCat

variable {σ σ' : Type}

/-- The inclusion `ι σ : EncCat σ ⥤ EncCat₂`, sending `f` to `(id, f)`. -/
@[simps]
def incl (σ : Type) : EncCat σ ⥤ EncCat₂ where
  obj X := ⟨σ, X.ast, X.rel⟩
  map f := ⟨id, f.fn, f.preserves⟩

instance : (incl σ).Faithful where
  map_injective h := hom_ext (congrArg EncCat₂.Hom.fn h)

theorem incl_obj_injective : Function.Injective (incl σ).obj := by
  rintro ⟨α, E⟩ ⟨β, F⟩ h
  change (⟨σ, α, E⟩ : EncCat₂) = ⟨σ, β, F⟩ at h
  simp only [EncCat₂.mk.injEq, true_and] at h
  obtain ⟨rfl, h⟩ := h
  cases eq_of_heq h
  rfl

/-- The object image of `ι σ` is exactly the carrier-`σ` objects of `EncCat₂`. -/
theorem incl_obj_surj {X : EncCat₂} (h : X.carrier = σ) : ∃ Y, (incl σ).obj Y = X := by
  obtain ⟨c, α, E⟩ := X
  change c = σ at h
  subst h
  exact ⟨⟨α, E⟩, rfl⟩

theorem incl_map_idOnCarrier {X Y : EncCat σ} (f : X ⟶ Y) :
    EncCat₂.IdOnCarrier ((incl σ).map f) := ⟨rfl, fun _ => HEq.rfl⟩

/-- Exactly the identity-on-carrier morphisms between included objects are in
the image of `ι σ`. -/
theorem idOnCarrier_iff_mem_range {X Y : EncCat σ} (f : (incl σ).obj X ⟶ (incl σ).obj Y) :
    EncCat₂.IdOnCarrier f ↔ ∃ g : X ⟶ Y, (incl σ).map g = f := by
  constructor
  · intro hf
    have hc : f.onCarrier = id := funext fun s => eq_of_heq (hf.2 s)
    refine ⟨⟨f.fn, fun s a h => ?_⟩, ?_⟩
    · have := f.preserves s a h
      rwa [hc] at this
    · exact EncCat₂.hom_ext hc.symm rfl
  · rintro ⟨g, rfl⟩
    exact incl_map_idOnCarrier g

/-- The subcategory of `EncCat₂` on carrier-`σ` objects (the image of
`incl σ`) with carrier function fixed to the identity. -/
abbrev Fixed (σ : Type) := InducedWideCategory EncCat₂ (incl σ).obj EncCat₂.IdOnCarrier

/-- `EncCat σ ⥤ Fixed σ`. -/
def toFixed (σ : Type) : EncCat σ ⥤ Fixed σ where
  obj X := X
  map f := ⟨(incl σ).map f, incl_map_idOnCarrier f⟩

/-- `Fixed σ ⥤ EncCat σ`: read off the syntax map. -/
def fromFixed (σ : Type) : Fixed σ ⥤ EncCat σ where
  obj X := X
  map {X Y} f := ⟨f.hom.fn, fun s a h => by
    have := f.hom.preserves s a h
    rwa [show f.hom.onCarrier s = s from eq_of_heq (f.property.2 s)] at this⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem toFixed_comp_fromFixed : toFixed σ ⋙ fromFixed σ = 𝟭 (EncCat σ) := rfl

theorem fromFixed_comp_toFixed : fromFixed σ ⋙ toFixed σ = 𝟭 (Fixed σ) := by
  refine Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  change (toFixed σ).map ((fromFixed σ).map f) = 𝟙 X ≫ f ≫ 𝟙 Y
  rw [Category.id_comp, Category.comp_id]
  apply InducedWideCategory.Hom.ext
  exact EncCat₂.hom_ext (funext fun s => (eq_of_heq (f.property.2 s)).symm) rfl

/-- `ι σ` factors as the isomorphism `toFixed σ` followed by the faithful
inclusion of the wide subcategory. -/
theorem toFixed_comp_inclusion :
    toFixed σ ⋙ wideInducedFunctor (incl σ).obj EncCat₂.IdOnCarrier = incl σ := rfl

/-- `EncCat σ` is isomorphic (in `Cat`) to `Fixed σ`.  The object half is
definitionally the identity (`Fixed σ` is `InducedWideCategory` over the
image of `incl σ`); the content is `idOnCarrier_iff_mem_range`.  See
`isoCarrierFiber` for the statement over all carrier-`σ` objects. -/
def isoFixed (σ : Type) : Cat.of (EncCat σ) ≅ Cat.of (Fixed σ) where
  hom := (toFixed σ).toCatHom
  inv := (fromFixed σ).toCatHom
  hom_inv_id := Cat.ext toFixed_comp_fromFixed
  inv_hom_id := Cat.ext fromFixed_comp_toFixed

/-! ## Carrier change commutes with `ι` up to `(g, id)` -/

/-- The `(g, id)` morphisms `ι X ⟶ ι (g_! X)`, natural in `X`. -/
def pushUnit (g : σ → σ') : incl σ ⟶ pushFunctor g ⋙ incl σ' where
  app _ := ⟨g, id, fun s _ h => ⟨s, rfl, h⟩⟩
  naturality _ _ _ := rfl

/-- The `(g, id)` morphisms `ι (g^* Y) ⟶ ι Y`, natural in `Y`. -/
def pullCounit (g : σ → σ') : pullFunctor g ⋙ incl σ ⟶ incl σ' where
  app _ := ⟨g, id, fun _ _ h => h⟩
  naturality _ _ _ := rfl

@[simp] theorem pushUnit_app_onCarrier (g : σ → σ') (X : EncCat σ) :
    ((pushUnit g).app X).onCarrier = g := rfl

@[simp] theorem pullCounit_app_onCarrier (g : σ → σ') (Y : EncCat σ') :
    ((pullCounit g).app Y).onCarrier = g := rfl

/-- `pushUnit` is cocartesian over `carrierFunctor`: every `EncCat₂` morphism
`(g, f) : ι X ⟶ ι Y` factors *uniquely* as `(g, id)` followed by the image
under `ι` of a morphism `g_! X ⟶ Y`. -/
theorem factor_through_push {X : EncCat σ} {Y' : EncCat σ'}
    (h : (incl σ).obj X ⟶ (incl σ').obj Y') :
    ∃! f : (pushFunctor h.onCarrier).obj X ⟶ Y',
      h = (pushUnit h.onCarrier).app X ≫ (incl σ').map f := by
  refine ⟨⟨h.fn, ?_⟩, rfl, fun _ hf => hom_ext (congrArg EncCat₂.Hom.fn hf).symm⟩
  rintro s' a ⟨s, rfl, hs⟩
  exact h.preserves s a hs

/-- `pullCounit` is cartesian over `carrierFunctor`: every `EncCat₂` morphism
`(g, f) : ι X ⟶ ι Y` factors *uniquely* as the image under `ι` of a morphism
`X ⟶ g^* Y` followed by `(g, id)`. -/
theorem factor_through_pull {X : EncCat σ} {Y : EncCat σ'}
    (h : (incl σ).obj X ⟶ (incl σ').obj Y) :
    ∃! f : X ⟶ (pullFunctor h.onCarrier).obj Y,
      h = (incl σ).map f ≫ (pullCounit h.onCarrier).app Y :=
  ⟨⟨h.fn, h.preserves⟩, rfl, fun _ hf => hom_ext (congrArg EncCat₂.Hom.fn hf).symm⟩

/-! ## `EncCat σ` as the fiber of `carrierFunctor` over `σ` -/

/-- Mathlib's fiber of `carrierFunctor` over `σ`: objects `{X // X.carrier = σ}`,
morphisms lying over `𝟙 σ`. -/
abbrev CarrierFiber (σ : Type) := EncCat₂.carrierFunctor.Fiber σ

theorem incl_comp_carrierFunctor (σ : Type) :
    incl σ ⋙ EncCat₂.carrierFunctor = (Functor.const (EncCat σ)).obj σ := rfl

/-- `ι σ`, corestricted to the fiber over `σ`. -/
def toCarrierFiber (σ : Type) : EncCat σ ⥤ CarrierFiber σ :=
  Functor.Fiber.inducedFunctor (incl_comp_carrierFunctor σ)

/-- A morphism of the fiber has the identity carrier map, up to the casts
along the objects' carrier equations. -/
theorem CarrierFiber.onCarrier_cast {X Y : CarrierFiber σ} (φ : X ⟶ Y) (s : σ) :
    φ.1.onCarrier (cast X.2.symm s) = cast Y.2.symm s := by
  obtain ⟨⟨c, α, E⟩, hX⟩ := X
  obtain ⟨⟨c', β, F⟩, hY⟩ := Y
  obtain ⟨φ, hφ⟩ := φ
  change c = σ at hX
  change c' = σ at hY
  subst hY
  subst hX
  have h := IsHomLift.fac' EncCat₂.carrierFunctor (𝟙 c) φ
  simp only [Category.id_comp] at h
  exact congrArg (fun k : c ⟶ c => k s) h

/-- Read a fiber object as an object of `EncCat σ`, casting the carrier. -/
def fromCarrierFiber (σ : Type) : CarrierFiber σ ⥤ EncCat σ where
  obj X := ⟨X.1.ast, fun s a => X.1.rel (cast X.2.symm s) a⟩
  map {X Y} φ := ⟨φ.1.fn, fun s a h => by
    have := φ.1.preserves _ _ h
    rwa [CarrierFiber.onCarrier_cast] at this⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem toCarrierFiber_comp_fromCarrierFiber :
    toCarrierFiber σ ⋙ fromCarrierFiber σ = 𝟭 (EncCat σ) := rfl

theorem fromCarrierFiber_comp_toCarrierFiber :
    fromCarrierFiber σ ⋙ toCarrierFiber σ = 𝟭 (CarrierFiber σ) := by
  refine Functor.ext (fun X => ?_) (fun X Y f => ?_)
  · obtain ⟨⟨c, α, E⟩, h⟩ := X
    change c = σ at h
    subst h
    rfl
  · obtain ⟨⟨c, α, E⟩, hX⟩ := X
    obtain ⟨⟨c', β, F⟩, hY⟩ := Y
    change c = σ at hX
    change c' = σ at hY
    subst hX hY
    apply Functor.Fiber.hom_ext
    simp only [Functor.map_comp, eqToHom_map]
    exact EncCat₂.hom_ext (funext fun s => (CarrierFiber.onCarrier_cast f s).symm) rfl

/-- **`EncCat σ` is isomorphic (in `Cat`) to the fiber of `carrierFunctor`
over `σ`**: the subcategory of `EncCat₂` of carrier-`σ` objects and morphisms
whose carrier map is `𝟙 σ`. -/
def isoCarrierFiber (σ : Type) : Cat.of (EncCat σ) ≅ Cat.of (CarrierFiber σ) where
  hom := (toCarrierFiber σ).toCatHom
  inv := (fromCarrierFiber σ).toCatHom
  hom_inv_id := Cat.ext toCarrierFiber_comp_fromCarrierFiber
  inv_hom_id := Cat.ext fromCarrierFiber_comp_toCarrierFiber

end EncCat

end Silmaril
