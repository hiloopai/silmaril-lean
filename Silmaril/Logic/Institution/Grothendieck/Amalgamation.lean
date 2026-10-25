module

public import Silmaril.Logic.Institution.Grothendieck.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

/-!
# Semi-exactness and model amalgamation

An institution is *semi-exact* when its model functor `Mod : Signᵒᵖ ⥤ Cat` takes pushouts of
signatures to pullbacks of model categories (Diaconescu, Definition 5; Goguen–Roşu,
Definition 3.10). Concretely: if `Σ'` is the pushout of `Σ₁ ← Σ → Σ₂`, then any two models
`M₁`, `M₂` that agree on `Σ` have exactly one amalgamation `M'` on `Σ'` (and likewise for model
homomorphisms). Amalgamation is what makes structured and heterogeneous specification
compositional; for Grothendieck institutions it is a hypothesis of the proof calculus of
heterogeneous development graphs.

With institutions as room functors, all of this is said by one predicate: `Amalgamates I f₁ f₂
g₁ g₂` states that the model categories of a commuting square of signatures form a pullback in
`Cat` (Mathlib's `IsPullback`), and `SemiExact I` asks this of every pushout square.

For comorphisms we record *exactness* (each naturality square of the model translation is a
pullback in `Cat`) and *weak exactness* (the existence half on objects).

The semi-exactness theorem for Grothendieck institutions is in
`Silmaril.Logic.Institution.Grothendieck.SemiExact`.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits

universe u₀ v₀ u v w m₁ m₂ u₁ v₁ u₂ v₂

section CatPullback

variable {P X Y Z : Cat.{v, u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Composing constant functors out of `W` with `F`, `G` gives equal morphisms of `Cat` when
the constants have equal images. -/
private lemma const_comp_eq {W A A' B : Cat.{v, u}} (F : A ⟶ B) (G : A' ⟶ B)
    (a : A) (b : A') (hab : F.toFunctor.obj a = G.toFunctor.obj b) :
    Cat.Hom.ofFunctor ((Functor.const W).obj a) ≫ F =
      Cat.Hom.ofFunctor ((Functor.const W).obj b) ≫ G := by
  apply CategoryTheory.Cat.ext
  refine CategoryTheory.Functor.ext (fun _ => hab) (fun _ _ _ => ?_)
  simp [Cat.Hom.comp_toFunctor]

/-- Objects of a pullback in `Cat` with the same projections are equal (the object functor
`Cat ⥤ Type` preserves the uniqueness half of pullbacks). -/
lemma _root_.CategoryTheory.IsPullback.cat_obj_ext (h : IsPullback fst snd f g) {p₁ p₂ : P}
    (h₁ : fst.toFunctor.obj p₁ = fst.toFunctor.obj p₂)
    (h₂ : snd.toFunctor.obj p₁ = snd.toFunctor.obj p₂) : p₁ = p₂ := by
  have e := h.hom_ext (W := P) (k := Cat.Hom.ofFunctor ((Functor.const P).obj p₁))
    (l := Cat.Hom.ofFunctor ((Functor.const P).obj p₂))
    (const_comp_eq _ _ _ _ h₁) (const_comp_eq _ _ _ _ h₂)
  exact congrArg (fun F : P ⟶ P => F.toFunctor.obj p₁) e

/-- In a pullback square of `Cat`, two objects agreeing over the base have exactly one common
lift (the object functor `Cat ⥤ Type` preserves pullbacks). -/
lemma _root_.CategoryTheory.IsPullback.cat_obj_existsUnique (h : IsPullback fst snd f g)
    (x : X) (y : Y) (hxy : f.toFunctor.obj x = g.toFunctor.obj y) :
    ∃! p : P, fst.toFunctor.obj p = x ∧ snd.toFunctor.obj p = y := by
  let kx : X ⟶ X := Cat.Hom.ofFunctor ((Functor.const X).obj x)
  let ky : X ⟶ Y := Cat.Hom.ofFunctor ((Functor.const X).obj y)
  have w : kx ≫ f = ky ≫ g := const_comp_eq (W := X) f g x y hxy
  refine ⟨(h.lift kx ky w).toFunctor.obj x, ⟨?_, ?_⟩, ?_⟩
  · exact congrArg (fun F : X ⟶ X => F.toFunctor.obj x) (h.lift_fst kx ky w)
  · exact congrArg (fun F : X ⟶ Y => F.toFunctor.obj x) (h.lift_snd kx ky w)
  · rintro p ⟨hp₁, hp₂⟩
    refine h.cat_obj_ext ?_ ?_
    · rw [hp₁]
      exact (congrArg (fun F : X ⟶ X => F.toFunctor.obj x) (h.lift_fst kx ky w)).symm
    · rw [hp₂]
      exact (congrArg (fun F : X ⟶ Y => F.toFunctor.obj x) (h.lift_snd kx ky w)).symm

end CatPullback

section Amalgamation

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- The model reduct functor of a signature morphism, as a morphism of `Cat`.

Source: `goguen-burstall-1992` in `references.bib`, §2.5, Definition 12 (the
model functor `𝒥 ; Left`). -/
def modHom {S S' : Sign} (σ : S ⟶ S') : (I.obj S').Mod ⟶ (I.obj S).Mod :=
  Cat.Hom.ofFunctor (I.map σ).mod

/-- A commuting square of signatures *amalgamates* when the corresponding square of model
categories is a pullback in `Cat`.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §2.2,
Definition 5 (printed page 6, PDF page 7: "semi-exact if and only if MOD preserves only
pullbacks"), for one square; `goguen-rosu-2002-institution-morphisms` in `references.bib`,
§3, Definition 3.10 (PDF page 10: "takes pushouts in Sign to pullbacks in Cat"). -/
def Amalgamates {S S₁ S₂ S' : Sign} (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂) (g₁ : S₁ ⟶ S') (g₂ : S₂ ⟶ S') :
    Prop :=
  IsPullback (modHom I g₁) (modHom I g₂) (modHom I f₁) (modHom I f₂)

/-- A room functor is semi-exact when every pushout square of signatures amalgamates.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §2.2,
Definition 5 (printed page 6, PDF page 7);
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10 (PDF
page 10); `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "(weakly) semi-exact, if any pushout of signatures is (weakly) amalgamable"). -/
def SemiExact : Prop :=
  ∀ ⦃S S₁ S₂ S' : Sign⦄ (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂) (g₁ : S₁ ⟶ S') (g₂ : S₂ ⟶ S'),
    IsPushout f₁ f₂ g₁ g₂ → Amalgamates I f₁ f₂ g₁ g₂

/-- Model amalgamation on objects: models agreeing on the common part have exactly one
amalgamation.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: a cocone is "amalgamable" when every consistent family of models has a unique
amalgamation), for a span. -/
def ModelAmalgamation {S S₁ S₂ S' : Sign} (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂) (g₁ : S₁ ⟶ S')
    (g₂ : S₂ ⟶ S') : Prop :=
  ∀ (M₁ : (I.obj S₁).Mod) (M₂ : (I.obj S₂).Mod),
    (I.map f₁).mod.obj M₁ = (I.map f₂).mod.obj M₂ →
      ∃! M' : (I.obj S').Mod, (I.map g₁).mod.obj M' = M₁ ∧ (I.map g₂).mod.obj M' = M₂

variable {I}

/-- An amalgamating square has unique amalgamation of models (the object functor `Cat ⥤ Type`
is representable, hence preserves pullbacks).

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "amalgamable, i.e. a … pullback"). -/
theorem Amalgamates.modelAmalgamation {S S₁ S₂ S' : Sign} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂}
    {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'} (h : Amalgamates I f₁ f₂ g₁ g₂) :
    ModelAmalgamation I f₁ f₂ g₁ g₂ := fun M₁ M₂ hM =>
  h.cat_obj_existsUnique M₁ M₂ hM

end Amalgamation

/-! ### Exact and weakly exact comorphisms -/

namespace Inst

variable {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}

/-- A comorphism is *exact* when every naturality square of its model translation,
`Mod_B(Φσ) ; β_Σ = β_{Σ'} ; Mod_A(σ)`, is a pullback in `Cat`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "(weakly) exact if, for each signature morphism `σ : Σ₁ → Σ₂` in `I₁`, the naturality
diagram … is (weakly) amalgamable, i.e. a (weak) pullback");
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §2.2.1,
Definition 7 (printed page 7, PDF page 8: exact institution embeddings; Diaconescu's square is
stated for an embedding `(Φ, Φ̄, ζ, α, β)` and becomes this one for the comorphism `(Φ̄, …)`
induced by the left adjoint `Φ̄`). -/
def CoHom.Exact (f : CoHom A B) : Prop :=
  ∀ ⦃S S' : A.Sign⦄ (σ : S ⟶ S'),
    IsPullback (modHom B.I (f.Φ.map σ)) (Cat.Hom.ofFunctor (f.ρ.app S').mod)
      (Cat.Hom.ofFunctor (f.ρ.app S).mod) (modHom A.I σ)

/-- A comorphism is *weakly exact* when, for every `σ : Σ ⟶ Σ'`, any `Σ'`-model `M₁'` and
`Φ(Σ)`-model `M₂` with `M₁'↾σ = β_Σ(M₂)` have a common expansion `M₂'` with `β_{Σ'}(M₂') = M₁'`
and `M₂'↾Φ(σ) = M₂`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.2,
Definition 4.9 (PDF pages 24–25; the printed `M₂ ∈ Mod^J(Φ(Σ₁))` is read as `Φ(Σ)`, the only
reading under which `β_Σ(M₂)` is defined);
`mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF page 5). -/
def CoHom.WeaklyExact (f : CoHom A B) : Prop :=
  ∀ ⦃S S' : A.Sign⦄ (σ : S ⟶ S') (M₁' : (A.I.obj S').Mod) (M₂ : (B.I.obj (f.Φ.obj S)).Mod),
    (A.I.map σ).mod.obj M₁' = (f.ρ.app S).mod.obj M₂ →
      ∃ M₂' : (B.I.obj (f.Φ.obj S')).Mod,
        (f.ρ.app S').mod.obj M₂' = M₁' ∧ (B.I.map (f.Φ.map σ)).mod.obj M₂' = M₂

/-- Exact comorphisms are weakly exact.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: weak exactness is the weak-pullback version of exactness). -/
theorem CoHom.Exact.weaklyExact {f : CoHom A B} (hf : f.Exact) : f.WeaklyExact := by
  intro S S' σ M₁' M₂ hM
  obtain ⟨M₂', ⟨h₁, h₂⟩, -⟩ := (hf σ).cat_obj_existsUnique M₂ M₁' hM.symm
  exact ⟨M₂', h₂, h₁⟩

end Inst

end Silmaril.Logic.Institution
