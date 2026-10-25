module

public import Silmaril.Logic.Institution.Morphism

@[expose] public section

/-!
# Theoroidal morphisms and comorphisms

Goguen–Roşu §5 generalize institution (co)morphisms from maps of signatures to maps of
theories. Using the institution of theories `Iᵗʰ` (`Inst.th`, `Theory.institution`):

* a functor `Ψ : Th(I) ⥤ Th(I')` is *signature preserving* when it lies over a functor of
  signatures `Φ`, i.e. `Ψ ⋙ sign' = sign ⋙ Φ` (Definition 5.2); `Φ` is then unique;
* a *theoroidal morphism (comorphism)* `I → I'` is a morphism (comorphism) `Iᵗʰ → I'ᵗʰ` whose
  functor on theories is signature preserving (Definition 5.3);
* a *simple theoroidal comorphism* is a comorphism `I → I'ᵗʰ` (Definition 5.7, see
  `Inst.SimpleTheoroidalCoHom`), and every ordinary comorphism is one, mapping each signature to
  the theory with no axioms (the remark after Definition 5.7), via the canonical comorphism
  `I → Iᵗʰ` sending `Σ` to `(Σ, ∅•)`.

## References

* `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, Definitions 5.1–5.3;
  §5.1, Definition 5.7 and the paragraph after it.
* `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
  footnote 11 (simple theoroidal corridors).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u v w m₁ m₂ u₁ v₁ u₂ v₂

/-! ### Signatures as theories with no axioms -/

section Empty

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- The presentation `(Σ, ∅)` with no axioms, functorially in `Σ`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1, after
Definition 5.7 ("signatures map to theories with no axioms"). -/
def Presentation.empty : Sign ⥤ Presentation I where
  obj S := ⟨S, ∅⟩
  map σ := ⟨σ, Set.mapsTo_empty _ _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The theory `(Σ, ∅•)` presented by no axioms, functorially in `Σ`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, the empty
theories `(Σ, ∅•)` of Propositions 5.4 and 5.5 (p. 17), and §5.1 after Definition 5.7. -/
def Theory.empty : Sign ⥤ Theory I := Presentation.empty I ⋙ Theory.ofPresentation I

/-- Every signature underlies a theory: `Theory.empty` is a section of the forgetful functor.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, after
Definition 5.2 (used for the uniqueness of the underlying signature functor). -/
theorem Theory.empty_forget : Theory.empty I ⋙ Theory.forget I = 𝟭 Sign :=
  rfl

/-- The canonical corridor from the room of `Σ` to the room of the theory `(Σ, ∅•)`: sentences
are unchanged and models of `∅•` are included into all `Σ`-models. -/
def Theory.emptyCorridor (S : Sign) :
    I.obj S ⟶ (Theory.institution I).obj ((Theory.empty I).obj S) :=
  ⟨id, ObjectProperty.ι (Theory.modelsProperty ((Theory.empty I).obj S).sentences),
    fun _ _ => Iff.rfl⟩

/-- The canonical comorphism `I → Iᵗʰ`, `Σ ↦ (Σ, ∅•)`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1, after
Definition 5.7 ("simple theoroidal (co)morphisms reduce to ordinary (co)morphisms where
signatures map to theories with no axioms"). -/
def Theory.toEmpty : I ⟶ Theory.empty I ⋙ Theory.institution I where
  app := Theory.emptyCorridor I
  naturality := by
    intro S S' σ
    exact Room.hom_ext rfl rfl

/-- Every model of `Σ` is a model of `∅•`: the canonical corridors are model-expansive (in fact
their model functors are isomorphisms of categories).

Source: `goguen-burstall-1992` in `references.bib`, §2.2, Proposition 3(5)
(`∅*** = ∅*`, i.e. every model satisfies `∅•`);
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6. -/
theorem Theory.toEmpty_modelExpansive (S : Sign) :
    Corridor.ModelExpansive ((Theory.toEmpty I).app S) := by
  intro M
  have hM : Theory.modelsProperty ((Theory.empty I).obj S).sentences M :=
    fun _ hφ => hφ M (fun ψ hψ => absurd hψ (Set.notMem_empty ψ))
  exact ⟨⟨M, hM⟩, rfl⟩

end Empty

/-! ### Signature-preserving functors and theoroidal (co)morphisms -/

section SignaturePreserving

variable {Sign : Type u₁} [Category.{v₁} Sign] {Sign' : Type u₂} [Category.{v₂} Sign']
  (I : Sign ⥤ Room.{w, m₁, m₂}) (I' : Sign' ⥤ Room.{w, m₁, m₂})

/-- A functor of theories `Ψ : Th(I) ⥤ Th(I')` is signature preserving when it lies over a
functor of signatures: `Ψ ⋙ sign' = sign ⋙ Φ`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, Definition 5.2. -/
structure SignaturePreserving (Ψ : Theory I ⥤ Theory I') where
  /-- The underlying functor of signatures `Φ`. -/
  base : Sign ⥤ Sign'
  /-- `Ψ ; sign' = sign ; Φ`. -/
  comm : Ψ ⋙ Theory.forget I' = Theory.forget I ⋙ base

variable {I I'}

/-- The underlying signature functor of a signature-preserving functor is unique.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, after
Definition 5.2 ("The reader may check that `Φ` is unique if it exists"). -/
theorem SignaturePreserving.base_unique {Ψ : Theory I ⥤ Theory I'}
    (h₁ h₂ : SignaturePreserving I I' Ψ) : h₁.base = h₂.base := by
  calc h₁.base = Theory.empty I ⋙ Theory.forget I ⋙ h₁.base := by
        rw [← Functor.assoc, Theory.empty_forget, Functor.id_comp]
    _ = Theory.empty I ⋙ Ψ ⋙ Theory.forget I' := by rw [h₁.comm]
    _ = Theory.empty I ⋙ Theory.forget I ⋙ h₂.base := by rw [h₂.comm]
    _ = h₂.base := by rw [← Functor.assoc, Theory.empty_forget, Functor.id_comp]

end SignaturePreserving

namespace Inst

/-- A theoroidal comorphism `A → B`: a comorphism `Aᵗʰ → Bᵗʰ` whose functor on theories is
signature preserving.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, Definition 5.3. -/
structure TheoroidalCoHom (A : Inst.{u₁, v₁, w, m₁, m₂}) (B : Inst.{u₂, v₂, w, m₁, m₂}) extends
    CoHom A.th B.th where
  /-- The functor on theories lies over a functor on signatures. -/
  sigPreserving : SignaturePreserving A.I B.I toCoHom.Φ

/-- A theoroidal morphism `A → B`: a morphism `Aᵗʰ → Bᵗʰ` whose functor on theories is
signature preserving.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5, Definition 5.3. -/
structure TheoroidalHom (A : Inst.{u₁, v₁, w, m₁, m₂}) (B : Inst.{u₂, v₂, w, m₁, m₂}) extends
    Hom A.th B.th where
  /-- The functor on theories lies over a functor on signatures. -/
  sigPreserving : SignaturePreserving A.I B.I toHom.Φ

/-- The canonical comorphism `A → Aᵗʰ`, sending each signature to its theory with no axioms.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1, after
Definition 5.7. -/
def toTh (A : Inst.{u, v, w, m₁, m₂}) : CoHom A A.th :=
  ⟨Theory.empty A.I, Theory.toEmpty A.I⟩

/-- Every comorphism is a simple theoroidal comorphism, mapping each signature `Σ` to the theory
`(ΦΣ, ∅•)` with no axioms.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1, after
Definition 5.7 ("simple theoroidal (co)morphisms reduce to ordinary (co)morphisms where
signatures map to theories with no axioms"). -/
def CoHom.toSimpleTheoroidal {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}
    (f : CoHom A B) : SimpleTheoroidalCoHom A B :=
  CoHom.comp f B.toTh

/-- The simple theoroidal comorphism of `f` maps each signature `Σ` to the theory `(ΦΣ, ∅•)`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1, after
Definition 5.7. -/
theorem CoHom.toSimpleTheoroidal_Φ {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}
    (f : CoHom A B) : f.toSimpleTheoroidal.Φ = f.Φ ⋙ Theory.empty B.I :=
  rfl

end Inst

end Silmaril.Logic.Institution
