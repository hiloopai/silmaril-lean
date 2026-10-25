module

public import Silmaril.Compile.Category.Valid

@[expose] public section

/-!
# The poset-enriched category of compilation relations

A morphism `L ⟶ L'` of `RelCat` is a *compilation relation*: a convention `c` together with a
relation between source and target programs contained in `Valid c`. Composition composes the
conventions and the relations; the lax law `valid_comp_le` is exactly what makes the composite
relation valid at the composite convention.

Hom-sets are partially ordered (conventions by refinement, relations by inclusion), and
composition is monotone, so `RelCat` is poset-enriched (a locally posetal 2-category). The
*valid relation* `validRel c = (c, Valid c)` is the top of the fibre over `c`, and the lax law
reads `validRel c ≫ validRel d ≤ validRel (c ≫ d)`.

## Main definitions

* `CompRel L L'`: a convention with a valid compilation relation.
* `RelCat`, its category instance, the partial order on hom-sets.
* `CompRel.validRel`: the maximal compilation relation at a convention.

## Main results

* `CompRel.comp_mono`: composition is monotone (poset enrichment).
* `CompRel.validRel_comp_le`: the lax law in `RelCat`.
* `CompRel.validRel_mono`: `validRel` is monotone in the convention.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

/-- A compilation relation at a convention: every related pair is a valid compilation. -/
@[ext]
structure CompRel (L L' : Language.{u}) : Type u where
  /-- The convention. -/
  conv : L ⟶ L'
  /-- The relation between source and target programs. -/
  rel : L.Prog → L'.Prog → Prop
  /-- Every related pair is valid at the convention. -/
  valid : rel ≤ Valid conv

namespace CompRel

variable {L L' L'' L''' : Language.{u}}

/-- The identity compilation relation: equality at the identity convention. -/
def id (L : Language.{u}) : CompRel L L where
  conv := 𝟙 L
  rel := (· = ·)
  valid p q h := by subst h; exact valid_id_refl p

/-- Composition of compilation relations: relational composition at the composite convention,
valid by the lax law. -/
def comp (f : CompRel L L') (g : CompRel L' L'') : CompRel L L'' where
  conv := f.conv ≫ g.conv
  rel := Relation.Comp f.rel g.rel
  valid p r h := by
    obtain ⟨q, h₁, h₂⟩ := h
    exact valid_comp_le f.conv g.conv p r ⟨q, f.valid p q h₁, g.valid q r h₂⟩

theorem id_comp (f : CompRel L L') : (id L).comp f = f :=
  CompRel.ext (Category.id_comp _) Relation.eq_comp

theorem comp_id (f : CompRel L L') : f.comp (id L') = f :=
  CompRel.ext (Category.comp_id _) Relation.comp_eq

theorem assoc (f : CompRel L L') (g : CompRel L' L'') (h : CompRel L'' L''') :
    (f.comp g).comp h = f.comp (g.comp h) :=
  CompRel.ext (Category.assoc _ _ _) Relation.comp_assoc

/-- Compilation relations are ordered by refinement of the convention and inclusion of the
relation. -/
instance : PartialOrder (CompRel L L') where
  le f g := f.conv ≤ g.conv ∧ f.rel ≤ g.rel
  le_refl f := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := CompRel.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

theorem le_def {f g : CompRel L L'} : f ≤ g ↔ f.conv ≤ g.conv ∧ f.rel ≤ g.rel := Iff.rfl

/-- Composition is monotone in both arguments: `RelCat` is poset-enriched. -/
theorem comp_mono {f f' : CompRel L L'} {g g' : CompRel L' L''} (hf : f ≤ f') (hg : g ≤ g') :
    f.comp g ≤ f'.comp g' := by
  rw [le_def, Convention.hom_le_def] at hf hg
  refine (le_def).2 ⟨Convention.hom_le_def.2
    ⟨by simp only [CompRel.comp, Convention.comp_Φ, hf.1.1, hg.1.1], ?_⟩, ?_⟩
  · rintro p r ⟨q, h₁, h₂⟩
    exact ⟨q, hf.1.2 _ _ h₁, hg.1.2 _ _ h₂⟩
  rintro p r ⟨q, h₁, h₂⟩
  exact ⟨q, hf.2 _ _ h₁, hg.2 _ _ h₂⟩

/-- The valid compilation relation at a convention: the top of the fibre over `c`. -/
def validRel (c : L ⟶ L') : CompRel L L' := ⟨c, Valid c, le_rfl⟩

/-- Every compilation relation lies below the valid relation of its convention. -/
theorem le_validRel (f : CompRel L L') : f ≤ validRel f.conv := ⟨le_rfl, f.valid⟩

/-- `validRel` is monotone in the convention order. -/
theorem validRel_mono {c d : L ⟶ L'} (h : c ≤ d) : validRel c ≤ validRel d :=
  ⟨h, valid_mono h⟩

/-- **The lax law in `RelCat`.** The direct valid relation at the composite convention contains
the composite of the valid relations. -/
theorem validRel_comp_le (c : L ⟶ L') (d : L' ⟶ L'') :
    (validRel c).comp (validRel d) ≤ validRel (c ≫ d) :=
  ⟨le_rfl, valid_comp_le c d⟩

/-- The lax law is strict in general. -/
theorem validRel_comp_ne :
    (validRel unitToEmpty).comp (validRel emptyToUnit) ≠ validRel (unitToEmpty ≫ emptyToUnit) := by
  intro h
  exact valid_comp_ne (congrArg CompRel.rel h)

/-- Identity law for `validRel`: the identity compilation relation lies below the valid relation
at the identity convention (refinement), and is strictly below it in general. -/
theorem id_le_validRel (L : Language.{u}) : id L ≤ validRel (𝟙 L) := le_validRel _

end CompRel

/-- The category of languages and compilation relations. -/
structure RelCat : Type (u + 1) where of ::
  /-- The underlying language. -/
  lang : Language.{u}

instance RelCat.category : Category.{u} RelCat.{u} where
  Hom X Y := CompRel X.lang Y.lang
  id X := CompRel.id X.lang
  comp f g := CompRel.comp f g
  id_comp := CompRel.id_comp
  comp_id := CompRel.comp_id
  assoc := CompRel.assoc

end Silmaril.Compile.Category
