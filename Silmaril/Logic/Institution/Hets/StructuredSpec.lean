module

public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

/-!
# Structured specifications over an arbitrary institution

The kernel language of Sannella and Tarlecki for structured specifications, over an institution
given as a room functor `I : Sign ⥤ Room`. Simultaneously with the specifications we define their
model classes (`StrSpec.models`):

* `basic Σ E` (presentations): the `Σ`-models of `E`;
* `union SP₁ SP₂` of two `Σ`-specifications: the intersection of the model classes;
* `translate σ SP` along `σ : Σ ⟶ Σ'`: the `Σ'`-models whose `σ`-reduct is a model of `SP`;
* `hide σ SP'` (Sannella–Tarlecki's `derive from SP' by σ`) along `σ : Σ ⟶ Σ'`: the
  `σ`-reducts of the models of the `Σ'`-specification `SP'`.

Over the Grothendieck institution of a logic graph (`Hets/Heterogeneous.lean`) the same language
is heterogeneous specification: translation and hiding along a Grothendieck signature morphism
`(d, σ)` move a specification along the comorphism `d`.

Two further notions are semantic: `StrSpec.Entails SP φ` (every model of `SP` satisfies `φ`)
and `StrSpec.Refines SP₁ SP₂` (every model of `SP₂` is a model of `SP₁`). The main results here
are the structured forms of borrowing: translation along a model-expansive corridor preserves and
reflects entailment and refinement (`entails_translate_iff`, `refines_translate_iff`;
Mossakowski's Proposition 5.2(2)), and hiding reduces entailment to the hidden specification
(`entails_hide_iff`).

Presentations in the sources have finite sets of axioms; `basic` allows any set.

## References

* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125, PDF
  page 127): the kernel language; §5.1 (printed page 126, PDF page 128): refinement; §5.2,
  Definition 5.1 and Proposition 5.2 (printed pages 126–127, PDF pages 128–129): borrowing.
* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1 (PDF
  page 19): the same kernel language.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- Structured specifications over the institution `I`, indexed by their signature.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127: presentations, union, translation, hiding);
`mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1 (PDF
page 19). -/
inductive StrSpec : Sign → Type (max u v w)
  /-- The presentation `⟨Σ, E⟩`. -/
  | basic (S : Sign) (E : Set (I.obj S).Sen) : StrSpec S
  /-- The union `SP₁ ∪ SP₂` of two `Σ`-specifications. -/
  | union {S : Sign} (SP₁ SP₂ : StrSpec S) : StrSpec S
  /-- `translate SP by σ`. -/
  | translate {S S' : Sign} (σ : S ⟶ S') (SP : StrSpec S) : StrSpec S'
  /-- `derive from SP' by σ` (hiding). -/
  | hide {S S' : Sign} (σ : S ⟶ S') (SP' : StrSpec S') : StrSpec S

namespace StrSpec

variable {I}

/-- The model class `Mod(SP)` of a structured specification.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127); `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`,
§8.1 (PDF page 19). -/
def models : {S : Sign} → StrSpec I S → Set (I.obj S).Mod
  | _, basic S E => (I.obj S).modelsOf E
  | _, union SP₁ SP₂ => SP₁.models ∩ SP₂.models
  | _, translate σ SP => (I.map σ).mod.obj ⁻¹' SP.models
  | _, hide σ SP' => (I.map σ).mod.obj '' SP'.models

@[simp] theorem models_basic (S : Sign) (E : Set (I.obj S).Sen) :
    (basic S E : StrSpec I S).models = (I.obj S).modelsOf E := rfl

@[simp] theorem models_union {S : Sign} (SP₁ SP₂ : StrSpec I S) :
    (union SP₁ SP₂).models = SP₁.models ∩ SP₂.models := rfl

@[simp] theorem models_translate {S S' : Sign} (σ : S ⟶ S') (SP : StrSpec I S) :
    (translate σ SP).models = (I.map σ).mod.obj ⁻¹' SP.models := rfl

@[simp] theorem models_hide {S S' : Sign} (σ : S ⟶ S') (SP' : StrSpec I S') :
    (hide σ SP').models = (I.map σ).mod.obj '' SP'.models := rfl

/-- Semantic consequence `SP ⊨_Σ φ`: every model of `SP` satisfies `φ`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Definition 5.1
(printed page 126, PDF page 128: `SP ⊨_Σ φ`). -/
def Entails {S : Sign} (SP : StrSpec I S) (φ : (I.obj S).Sen) : Prop :=
  ∀ M ∈ SP.models, (I.obj S).Sat M φ

/-- Refinement `SP₁ ⇝ SP₂`: every model of `SP₂` is a model of `SP₁`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 126,
PDF page 128: "`SP₂` refines `SP₁` … if `Mod(SP₂) ⊆ Mod(SP₁)`"). -/
def Refines {S : Sign} (SP₁ SP₂ : StrSpec I S) : Prop :=
  SP₂.models ⊆ SP₁.models

/-- Entailment from a presentation is semantic consequence in the institution. -/
theorem entails_basic_iff (S : Sign) (E : Set (I.obj S).Sen) (φ : (I.obj S).Sen) :
    (basic S E : StrSpec I S).Entails φ ↔ (I.obj S).Entails E φ :=
  ⟨fun h M hM => h M hM, fun h M hM => h M hM⟩

/-- A union entails what either part entails. -/
theorem Entails.union_left {S : Sign} {SP₁ : StrSpec I S} (SP₂ : StrSpec I S)
    {φ : (I.obj S).Sen} (h : SP₁.Entails φ) : (union SP₁ SP₂).Entails φ :=
  fun M hM => h M hM.1

/-- Translation preserves entailment: `SP ⊨ φ` implies `translate SP by σ ⊨ σ(φ)`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127), by the satisfaction condition. -/
theorem Entails.translate {S S' : Sign} (σ : S ⟶ S') {SP : StrSpec I S} {φ : (I.obj S).Sen}
    (h : SP.Entails φ) : (translate σ SP).Entails ((I.map σ).sen φ) :=
  fun M hM => ((I.map σ).sat M φ).2 (h _ hM)

/-- **Borrowing of entailment for structured specifications.** Along a signature morphism
whose corridor is model-expansive, translation preserves and reflects entailment.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Definition 5.1 and
Proposition 5.2(2) (printed pages 126–127, PDF pages 128–129): here
`β⁻¹(Mod(SP)) = Mod(translate SP by σ)` holds by definition. -/
theorem entails_translate_iff {S S' : Sign} (σ : S ⟶ S')
    (hσ : Corridor.ModelExpansive (I.map σ)) (SP : StrSpec I S) (φ : (I.obj S).Sen) :
    SP.Entails φ ↔ (translate σ SP).Entails ((I.map σ).sen φ) := by
  refine ⟨Entails.translate σ, fun h M hM => ?_⟩
  obtain ⟨M', rfl⟩ := hσ M
  exact ((I.map σ).sat M' φ).1 (h M' hM)

/-- **Borrowing of refinement for structured specifications.** Along a signature morphism
whose corridor is model-expansive, translation preserves and reflects refinement.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Definition 5.1 and
Proposition 5.2(2) (printed pages 126–127, PDF pages 128–129). -/
theorem refines_translate_iff {S S' : Sign} (σ : S ⟶ S')
    (hσ : Corridor.ModelExpansive (I.map σ)) (SP₁ SP₂ : StrSpec I S) :
    SP₁.Refines SP₂ ↔ (translate σ SP₁).Refines (translate σ SP₂) := by
  refine ⟨fun h M hM => h hM, fun h M hM => ?_⟩
  obtain ⟨M', rfl⟩ := hσ M
  exact h (show M' ∈ (translate σ SP₂).models from hM)

/-- Entailment of a hiding: `derive from SP' by σ ⊨ φ` iff `SP' ⊨ σ(φ)`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127), by the satisfaction condition. -/
theorem entails_hide_iff {S S' : Sign} (σ : S ⟶ S') (SP' : StrSpec I S') (φ : (I.obj S).Sen) :
    (hide σ SP').Entails φ ↔ SP'.Entails ((I.map σ).sen φ) := by
  constructor
  · intro h M' hM'
    exact ((I.map σ).sat M' φ).2 (h _ ⟨M', hM', rfl⟩)
  · rintro h _ ⟨M', hM', rfl⟩
    exact ((I.map σ).sat M' φ).1 (h M' hM')

/-- Hiding what was just translated along a model-expansive corridor gives back the original
model class.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, proof of
Proposition 5.2(2) (printed page 127, PDF page 129: "`β_Σ(β_Σ⁻¹(𝓜)) = 𝓜`"). -/
theorem models_hide_translate {S S' : Sign} (σ : S ⟶ S')
    (hσ : Corridor.ModelExpansive (I.map σ)) (SP : StrSpec I S) :
    (hide σ (translate σ SP)).models = SP.models :=
  Set.image_preimage_eq _ hσ

end StrSpec

end Silmaril.Logic.Institution
