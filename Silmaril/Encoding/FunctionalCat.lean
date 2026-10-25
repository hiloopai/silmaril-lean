module

public import Silmaril.Encoding.Encoded
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The functional and deterministic subcategories of `EncCat`

`Encoded.text_injective_iff` says the projection `Encoded E → σ` is injective
exactly when `E` is functional — the "projection to the text is an injection"
property of `WithText` / `WithBinary` (and so of `WasmText` / `WasmBinary`).
This module gives it categorical form.

* `FunEncCat σ` is the full subcategory of `EncCat σ` on functional objects
  (Mathlib `ObjectProperty.FullSubcategory`), with inclusion `FunEncCat.ι σ`;
  dually `DetEncCat σ` on deterministic objects.
* **Characterization**: an object `X : EncCat σ` is functional iff the component
  `(Encoded.textNat σ).app X` is a monomorphism in `Type`
  (`EncCat.functional_iff_mono_textNat_app`), and deterministic iff
  `(Encoded.astNat σ).app X` is mono (`EncCat.deterministic_iff_mono_astNat_app`).
  Consequently the whiskered transformations `ι ◁ textNat` (on `FunEncCat`)
  and `ι ◁ astNat` (on `DetEncCat`) are monomorphisms of functors.
* **Closure under carrier change**: `pushFunctor g` restricts to `FunEncCat`
  for injective `g` and `pullFunctor g` always does (`FunEncCat.pushFunctor`,
  `FunEncCat.pullFunctor`); dually `pushFunctor g` always restricts to
  `DetEncCat` and `pullFunctor g` does for injective `g`.  The restrictions
  commute strictly with the inclusions.
* **Bundled functional encodings**: `FunEncRel.toFunEncCat` sends `E` to an
  object of `FunEncCat σ`; `FunEncRel.Encoded E` is definitionally
  `(Encoded.functor σ).obj` of it, and `FunEncRel.textEmbedding` is the
  `textNat` component.
* **Varying carrier**: `FunEncCat₂` is the full subcategory of `EncCat₂` on
  functional objects; there `Encoded.textNat₂` is componentwise mono, and
  again a component is mono exactly on functional objects.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

/-- A natural transformation whose components are all monomorphisms is a
monomorphism of functors (no limits needed). -/
theorem NatTrans.mono_of_forall_mono_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) (h : ∀ X, Mono (α.app X)) : Mono α :=
  ⟨fun g k e => by
    ext X
    exact (cancel_mono (α.app X)).mp (by simpa using congrArg (fun t => t.app X) e)⟩

namespace EncCat

variable {σ σ' : Type}

/-- The property of an object of `EncCat σ` of being functional. -/
def IsFunctional (σ : Type) : ObjectProperty (EncCat σ) := fun X => X.rel.Functional

/-- The property of an object of `EncCat σ` of being deterministic. -/
def IsDeterministic (σ : Type) : ObjectProperty (EncCat σ) := fun X => X.rel.Deterministic

/-- **Functional objects are exactly those whose `textNat` component is a
monomorphism.** -/
theorem functional_iff_mono_textNat_app (X : EncCat σ) :
    X.rel.Functional ↔ Mono ((Encoded.textNat σ).app X) := by
  rw [← Encoded.text_injective_iff]
  exact (CategoryTheory.ofHom_mono_iff_injective _).symm

/-- **Deterministic objects are exactly those whose `astNat` component is a
monomorphism.** -/
theorem deterministic_iff_mono_astNat_app (X : EncCat σ) :
    X.rel.Deterministic ↔ Mono ((Encoded.astNat σ).app X) := by
  rw [← Encoded.ast_injective_iff]
  exact (CategoryTheory.ofHom_mono_iff_injective _).symm

end EncCat

/-- The full subcategory of `EncCat σ` on functional encodings. -/
abbrev FunEncCat (σ : Type) := (EncCat.IsFunctional σ).FullSubcategory

/-- The full subcategory of `EncCat σ` on deterministic encodings. -/
abbrev DetEncCat (σ : Type) := (EncCat.IsDeterministic σ).FullSubcategory

namespace FunEncCat

variable {σ σ' : Type}

/-- The (fully faithful) inclusion `FunEncCat σ ⥤ EncCat σ`. -/
abbrev ι (σ : Type) : FunEncCat σ ⥤ EncCat σ := (EncCat.IsFunctional σ).ι

/-- The `textNat` component at an object of `FunEncCat σ` is injective. -/
theorem textNat_app_injective (X : FunEncCat σ) :
    Function.Injective ((Encoded.textNat σ).app X.obj) :=
  Encoded.text_injective X.property

instance (X : FunEncCat σ) : Mono ((Encoded.textNat σ).app X.obj) :=
  (EncCat.functional_iff_mono_textNat_app X.obj).mp X.property

/-- **`FunEncCat σ` is characterized by `textNat`**: an object of `EncCat σ`
lies in it iff its `textNat` component is mono. -/
theorem mem_iff_mono_textNat_app (X : EncCat σ) :
    EncCat.IsFunctional σ X ↔ Mono ((Encoded.textNat σ).app X) :=
  EncCat.functional_iff_mono_textNat_app X

/-- Restricted to functional encodings, `text : Encoded ⟶ const σ` is a
monomorphism of functors. -/
instance mono_whiskerLeft_textNat :
    Mono (Functor.whiskerLeft (ι σ) (Encoded.textNat σ)) :=
  NatTrans.mono_of_forall_mono_app _ fun X =>
    inferInstanceAs (Mono ((Encoded.textNat σ).app X.obj))

/-- Pushforward along an injective carrier map, restricted to functional
encodings. -/
def pushFunctor {g : σ → σ'} (hg : Function.Injective g) : FunEncCat σ ⥤ FunEncCat σ' :=
  (EncCat.IsFunctional σ').lift (ι σ ⋙ EncCat.pushFunctor g) fun X => X.property.push hg

/-- Pullback along any carrier map, restricted to functional encodings. -/
def pullFunctor (g : σ → σ') : FunEncCat σ' ⥤ FunEncCat σ :=
  (EncCat.IsFunctional σ).lift (ι σ' ⋙ EncCat.pullFunctor g) fun X => X.property.pull g

theorem pushFunctor_comp_ι {g : σ → σ'} (hg : Function.Injective g) :
    pushFunctor hg ⋙ ι σ' = ι σ ⋙ EncCat.pushFunctor g := rfl

theorem pullFunctor_comp_ι (g : σ → σ') :
    pullFunctor g ⋙ ι σ = ι σ' ⋙ EncCat.pullFunctor g := rfl

end FunEncCat

namespace DetEncCat

variable {σ σ' : Type}

/-- The (fully faithful) inclusion `DetEncCat σ ⥤ EncCat σ`. -/
abbrev ι (σ : Type) : DetEncCat σ ⥤ EncCat σ := (EncCat.IsDeterministic σ).ι

theorem astNat_app_injective (X : DetEncCat σ) :
    Function.Injective ((Encoded.astNat σ).app X.obj) :=
  Encoded.ast_injective_iff.mpr X.property

instance (X : DetEncCat σ) : Mono ((Encoded.astNat σ).app X.obj) :=
  (EncCat.deterministic_iff_mono_astNat_app X.obj).mp X.property

/-- **`DetEncCat σ` is characterized by `astNat`**: an object of `EncCat σ`
lies in it iff its `astNat` component is mono. -/
theorem mem_iff_mono_astNat_app (X : EncCat σ) :
    EncCat.IsDeterministic σ X ↔ Mono ((Encoded.astNat σ).app X) :=
  EncCat.deterministic_iff_mono_astNat_app X

/-- Restricted to deterministic encodings, `ast : Encoded ⟶ forget` is a
monomorphism of functors. -/
instance mono_whiskerLeft_astNat :
    Mono (Functor.whiskerLeft (ι σ) (Encoded.astNat σ)) :=
  NatTrans.mono_of_forall_mono_app _ fun X =>
    inferInstanceAs (Mono ((Encoded.astNat σ).app X.obj))

/-- Pushforward along any carrier map, restricted to deterministic encodings. -/
def pushFunctor (g : σ → σ') : DetEncCat σ ⥤ DetEncCat σ' :=
  (EncCat.IsDeterministic σ').lift (ι σ ⋙ EncCat.pushFunctor g) fun X => X.property.push g

/-- Pullback along an injective carrier map, restricted to deterministic
encodings. -/
def pullFunctor {g : σ → σ'} (hg : Function.Injective g) : DetEncCat σ' ⥤ DetEncCat σ :=
  (EncCat.IsDeterministic σ).lift (ι σ' ⋙ EncCat.pullFunctor g) fun X => X.property.pull hg

theorem pushFunctor_comp_ι (g : σ → σ') :
    pushFunctor g ⋙ ι σ' = ι σ ⋙ EncCat.pushFunctor g := rfl

theorem pullFunctor_comp_ι {g : σ → σ'} (hg : Function.Injective g) :
    pullFunctor hg ⋙ ι σ = ι σ' ⋙ EncCat.pullFunctor g := rfl

end DetEncCat

/-! ## Bundled functional encodings as objects -/

namespace FunEncRel

variable {σ α : Type}

/-- A bundled functional encoding as an object of `FunEncCat σ`. -/
def toFunEncCat (E : FunEncRel σ α) : FunEncCat σ := ⟨EncCat.of α E.rel, E.functional⟩

@[simp] theorem toFunEncCat_obj (E : FunEncRel σ α) :
    E.toFunEncCat.obj = EncCat.of α E.rel := rfl

/-- `FunEncRel.Encoded E` is `Encoded.functor` at the bundled object. -/
theorem encoded_eq_functor_obj (E : FunEncRel σ α) :
    E.Encoded = (Encoded.functor σ).obj ((FunEncCat.ι σ).obj E.toFunEncCat) := rfl

/-- `FunEncRel.textEmbedding` is the `textNat` component at the bundled
object. -/
theorem textEmbedding_eq_textNat_app (E : FunEncRel σ α) (x : E.Encoded) :
    E.textEmbedding x = (Encoded.textNat σ).app ((FunEncCat.ι σ).obj E.toFunEncCat) x := rfl

end FunEncRel

/-! ## Varying carrier -/

namespace EncCat₂

/-- The property of an object of `EncCat₂` of being functional. -/
def IsFunctional : ObjectProperty EncCat₂ := fun X => X.rel.Functional

/-- An object of `EncCat₂` is functional iff its `textNat₂` component is
mono. -/
theorem functional_iff_mono_textNat₂_app (X : EncCat₂) :
    X.rel.Functional ↔ Mono (Encoded.textNat₂.app X) := by
  rw [← Encoded.text_injective_iff]
  exact (CategoryTheory.ofHom_mono_iff_injective _).symm

end EncCat₂

/-- The full subcategory of `EncCat₂` on functional encodings. -/
abbrev FunEncCat₂ := EncCat₂.IsFunctional.FullSubcategory

namespace FunEncCat₂

/-- The inclusion `FunEncCat₂ ⥤ EncCat₂`. -/
abbrev ι : FunEncCat₂ ⥤ EncCat₂ := EncCat₂.IsFunctional.ι

instance (X : FunEncCat₂) : Mono (Encoded.textNat₂.app X.obj) :=
  (EncCat₂.functional_iff_mono_textNat₂_app X.obj).mp X.property

/-- Restricted to functional encodings, `textNat₂` is a monomorphism of
functors. -/
instance mono_whiskerLeft_textNat₂ : Mono (Functor.whiskerLeft ι Encoded.textNat₂) :=
  NatTrans.mono_of_forall_mono_app _ fun X =>
    inferInstanceAs (Mono (Encoded.textNat₂.app X.obj))

/-- `EncCat.incl σ` restricts to `FunEncCat σ ⥤ FunEncCat₂`. -/
def inclFun (σ : Type) : FunEncCat σ ⥤ FunEncCat₂ :=
  EncCat₂.IsFunctional.lift (FunEncCat.ι σ ⋙ EncCat.incl σ) fun X => X.property

theorem inclFun_comp_ι (σ : Type) : inclFun σ ⋙ ι = FunEncCat.ι σ ⋙ EncCat.incl σ := rfl

end FunEncCat₂

end Silmaril
