module

public import Silmaril.Logic.Institution.Borrowing
public import Mathlib.Order.Closure

@[expose] public section

/-!
# Entailment relations, entailment systems and logics

The proof-theoretic counterpart of rooms and institutions, following Mossakowski, Diaconescu and
Tarlecki (`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`).

* An *entailment relation* (ER) `(S, ⊢)` is a Tarskian consequence relation on a set of
  sentences: reflexive, monotone and transitive (Definition 2.1). ER morphisms translate
  sentences and preserve `⊢`; they are *conservative* when they also reflect it
  (Definition 2.3). ERs and their morphisms form a category `ER`.
* The semantic entailment of a room is an ER (Proposition 3.2, `Room.semanticER`), and a corridor
  is an ER morphism between the semantic ERs (Proposition 3.7, `Room.semanticFunctor`).
* An *entailment system* is a functor `Sign ⥤ ER` (Definition 4.1), just as an institution is a
  functor `Sign ⥤ Room` (Definition 4.2).
* A *logic* is an institution together with an entailment system agreeing on signatures and
  sentences; it is *sound* when `Γ ⊢_Σ φ` implies `Γ ⊨_Σ φ` and *complete* for the converse
  (§4, after Definition 4.2). `LogicalSystem` bundles a room functor with a derivability relation on its
  sentences; `LogicalSystem.entailmentSystem` is the functor `Sign ⥤ ER`, and
  `LogicalSystem.entailmentSystem_comp_senFunctor` says that it agrees with the institution on sentences.
* A *logic comorphism* is an institution comorphism whose sentence translations are ER morphisms
  (§4.1, Definition 4.3 and the paragraph after it). `LogicalSystem.CoHom.sound_of_sound`: a
  model-expansive logic comorphism into a sound logic comes from a sound logic.
* A theory `Γ` is *inconsistent* ("trivial" in Carnielli–D'Ottaviano, MDT reference [10],
  footnote 3) when it derives every sentence (§2.2).

This is the layer on which the prover metatheory of `Silmaril.Logic.HOLLight` and
`Silmaril.Logic.Metamath` is restated (`Metatheory.HOL`, `Metatheory.Consilience`,
`Metatheory.Metamath`, `Metatheory.HolMM`).
-/

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory

universe u v w m₁ m₂ u₁ v₁ u₂ v₂

/-- A Tarskian entailment relation `(S, ⊢)`: reflexive, monotone and transitive. Transitivity is
stated with a set `Δ` of lemmas in place of the indexed family `{φᵢ | i ∈ I}`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.1. -/
structure ER : Type (w + 1) where
  /-- The sentences. -/
  Sen : Type w
  /-- Entailment `Γ ⊢ φ`. -/
  Derives : Set Sen → Sen → Prop
  /-- Reflexivity: `{φ} ⊢ φ`. -/
  refl : ∀ φ, Derives {φ} φ
  /-- Monotonicity: `Γ ⊢ φ` and `Γ ⊆ Γ'` give `Γ' ⊢ φ`. -/
  mono : ∀ {Γ Γ' : Set Sen} {φ : Sen}, Γ ⊆ Γ' → Derives Γ φ → Derives Γ' φ
  /-- Transitivity: `Γ ⊢ φ` for every `φ ∈ Δ` and `Γ ∪ Δ ⊢ ψ` give `Γ ⊢ ψ`. -/
  trans : ∀ {Γ Δ : Set Sen} {ψ : Sen}, (∀ φ ∈ Δ, Derives Γ φ) → Derives (Γ ∪ Δ) ψ →
    Derives Γ ψ

namespace ER

/-- A morphism of entailment relations: a sentence translation preserving `⊢`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.3. -/
structure Hom (S₁ S₂ : ER.{w}) : Type w where
  /-- The sentence translation `α`. -/
  sen : S₁.Sen → S₂.Sen
  /-- `Γ ⊢₁ φ` implies `α(Γ) ⊢₂ α(φ)`. -/
  map_derives : ∀ {Γ : Set S₁.Sen} {φ : S₁.Sen}, S₁.Derives Γ φ → S₂.Derives (sen '' Γ) (sen φ)

theorem Hom.ext' {S₁ S₂ : ER.{w}} {f g : Hom S₁ S₂} (h : f.sen = g.sen) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- An ER morphism is conservative when it also reflects entailment:
`α(Γ) ⊢₂ α(φ)` implies `Γ ⊢₁ φ`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.3 (last sentence). -/
def Hom.Conservative {S₁ S₂ : ER.{w}} (f : Hom S₁ S₂) : Prop :=
  ∀ (Γ : Set S₁.Sen) (φ : S₁.Sen), S₂.Derives (f.sen '' Γ) (f.sen φ) → S₁.Derives Γ φ

/-- Entailment relations and their morphisms form the category `ER`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
after Definition 2.3 ("ERs and ER morphisms form a category ER"). -/
instance category : Category.{w} ER.{w} where
  Hom := Hom
  id S := ⟨id, fun h => by rw [Set.image_id]; exact h⟩
  comp f g := ⟨g.sen ∘ f.sen, fun h => by rw [Set.image_comp]; exact g.map_derives (f.map_derives h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[ext]
theorem hom_ext {S₁ S₂ : ER.{w}} {f g : S₁ ⟶ S₂} (h : f.sen = g.sen) : f = g := Hom.ext' h

@[simp] theorem id_sen (S : ER.{w}) : (𝟙 S : S ⟶ S).sen = id := rfl

@[simp] theorem comp_sen {S₁ S₂ S₃ : ER.{w}} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (f ≫ g).sen = g.sen ∘ f.sen := rfl

/-- The sentence functor `ER ⥤ Type`. -/
def senFunctor : ER.{w} ⥤ Type w where
  obj S := S.Sen
  map f := TypeCat.ofHom f.sen
  map_id _ := rfl
  map_comp _ _ := rfl

variable (S : ER.{w})

/-- A theory `Γ` is consistent when it does not derive some sentence.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2.2,
first paragraph. -/
def Consistent (Γ : Set S.Sen) : Prop := ∃ φ, ¬ S.Derives Γ φ

/-- A theory `Γ` is inconsistent ("trivial", footnote 3) when it derives every sentence.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2.2,
first paragraph and footnote 3. -/
def Inconsistent (Γ : Set S.Sen) : Prop := ∀ φ, S.Derives Γ φ

theorem not_consistent_iff (Γ : Set S.Sen) : ¬ S.Consistent Γ ↔ S.Inconsistent Γ := by
  simp [Consistent, Inconsistent]

/-- `Γ` derives every sentence satisfying `P`: triviality relative to a class of sentences
(for example the well-typed Boolean sequents of a HOL presentation). `Inconsistent` is the case
`P = ⊤`. -/
def TrivialOn (Γ : Set S.Sen) (P : S.Sen → Prop) : Prop := ∀ φ, P φ → S.Derives Γ φ

theorem trivialOn_top_iff (Γ : Set S.Sen) : S.TrivialOn Γ (fun _ => True) ↔ S.Inconsistent Γ :=
  ⟨fun h φ => h φ trivial, fun h φ _ => h φ⟩

/-- The closure operator `Γ ↦ {φ | Γ ⊢ φ}` of an entailment relation (Mathlib's
`ClosureOperator` on `Set S.Sen`): ERs are closure operators.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.5 and Proposition 2.6 (p. 4). -/
def closure : ClosureOperator (Set S.Sen) :=
  ClosureOperator.mk' (fun Γ => {φ | S.Derives Γ φ})
    (fun _ _ h _ hφ => S.mono h hφ)
    (fun _ φ hφ => S.mono (Set.singleton_subset_iff.mpr hφ) (S.refl φ))
    (fun Γ _ hψ => S.trans (Δ := {φ | S.Derives Γ φ}) (fun _ h => h)
      (S.mono Set.subset_union_right hψ))

theorem mem_closure_iff {Γ : Set S.Sen} {φ : S.Sen} : φ ∈ S.closure Γ ↔ S.Derives Γ φ :=
  Iff.rfl

end ER

/-! ### Rooms: semantic entailment and soundness -/

end Silmaril.Logic.Institution.Metatheory

namespace Silmaril.Logic.Institution.Room

open CategoryTheory Silmaril.Logic.Institution.Metatheory

universe w m₁ m₂

variable (R : Room.{w, m₁, m₂})

/-- Semantic entailment in a room is a Tarskian entailment relation.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.2. -/
def semanticER : ER.{w} where
  Sen := R.Sen
  Derives := R.Entails
  refl φ _ hM := hM φ (Set.mem_singleton φ)
  mono h hd M hM := hd M fun ψ hψ => hM ψ (h hψ)
  trans hΔ hd M hM := hd M fun ψ hψ => hψ.elim (hM ψ) fun h => hΔ ψ h M hM

/-- A corridor is an ER morphism between the semantic entailment relations.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7 (first claim). -/
def semanticFunctor : Room.{w, m₁, m₂} ⥤ ER.{w} where
  obj R := R.semanticER
  map c := ⟨c.sen, fun h => Corridor.entails_map c h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A derivability relation on the sentences of a room is sound when it is contained in
semantic entailment: the logic room `(S, M, ⊨, ⊢)` is sound.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.3. -/
def IsSound (D : Set R.Sen → R.Sen → Prop) : Prop := ∀ Γ φ, D Γ φ → R.Entails Γ φ

/-- A derivability relation on the sentences of a room is complete when it contains semantic
entailment.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.3. -/
def IsComplete (D : Set R.Sen → R.Sen → Prop) : Prop := ∀ Γ φ, R.Entails Γ φ → D Γ φ

end Silmaril.Logic.Institution.Room

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory

universe u v w m₁ m₂ u₁ v₁ u₂ v₂

/-! ### Entailment systems and logics -/

/-- An entailment system (a π-institution) is a functor `Sign ⥤ ER`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.1. -/
abbrev EntailmentSystem (Sign : Type u) [Category.{v} Sign] : Type _ := Sign ⥤ ER.{w}

/-- A logic: an institution `I : Sign ⥤ Room` together with an entailment relation on the
sentences of each room, preserved by the sentence translations of signature morphisms. Its
entailment system is `LogicalSystem.entailmentSystem`; by construction it agrees with `I` on signatures
and sentences.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2 ("A logic is an institution together with an entailment
system agreeing on their signature and sentence parts"). -/
structure LogicalSystem.{u', v', w', m₁', m₂'} (Sign : Type u') [Category.{v'} Sign] where
  /-- The institution. -/
  I : Sign ⥤ Room.{w', m₁', m₂'}
  /-- Derivability `Γ ⊢_Σ φ`. -/
  Derives : (S : Sign) → Set (I.obj S).Sen → (I.obj S).Sen → Prop
  refl : ∀ S φ, Derives S {φ} φ
  mono : ∀ S {Γ Γ' : Set (I.obj S).Sen} {φ}, Γ ⊆ Γ' → Derives S Γ φ → Derives S Γ' φ
  trans : ∀ S {Γ Δ : Set (I.obj S).Sen} {ψ}, (∀ φ ∈ Δ, Derives S Γ φ) → Derives S (Γ ∪ Δ) ψ →
    Derives S Γ ψ
  /-- Translation along signature morphisms preserves derivability. -/
  map_derives : ∀ {S S' : Sign} (σ : S ⟶ S') {Γ φ}, Derives S Γ φ →
    Derives S' ((I.map σ).sen '' Γ) ((I.map σ).sen φ)

namespace LogicalSystem

variable {Sign : Type u} [Category.{v} Sign] (L : LogicalSystem.{u, v, w, m₁, m₂} Sign)

/-- The entailment relation of a logic at a signature. -/
def er (S : Sign) : ER.{w} where
  Sen := (L.I.obj S).Sen
  Derives := L.Derives S
  refl := L.refl S
  mono := L.mono S
  trans := L.trans S

/-- The entailment system of a logic, a functor `Sign ⥤ ER`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.1. -/
def entailmentSystem : Sign ⥤ ER.{w} where
  obj := L.er
  map σ := ⟨(L.I.map σ).sen, L.map_derives σ⟩
  map_id S := ER.hom_ext (congrArg Corridor.sen (L.I.map_id S))
  map_comp σ τ := ER.hom_ext (congrArg Corridor.sen (L.I.map_comp σ τ))

/-- The entailment system and the institution of a logic agree on sentences.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2. -/
theorem entailmentSystem_comp_senFunctor :
    L.entailmentSystem ⋙ ER.senFunctor = L.I ⋙ Room.senFunctor :=
  rfl

/-- A logic is sound when `Γ ⊢_Σ φ` implies `Γ ⊨_Σ φ` at every signature.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2. -/
def Sound : Prop := ∀ S, (L.I.obj S).IsSound (L.Derives S)

/-- A logic is complete when `Γ ⊨_Σ φ` implies `Γ ⊢_Σ φ` at every signature.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2. -/
def Complete : Prop := ∀ S, (L.I.obj S).IsComplete (L.Derives S)

/-- The bundled institution of a logic. -/
def toInst : Inst.{u, v, w, m₁, m₂} := ⟨Sign, L.I⟩

/-! ### Logic comorphisms -/

variable {Sign₁ : Type u₁} [Category.{v₁} Sign₁] {Sign₂ : Type u₂} [Category.{v₂} Sign₂]

/-- A logic comorphism `(Φ, ρ) : A → B`: an institution comorphism (`ρ : I_A ⟶ Φ ⋙ I_B`) whose
sentence translations are ER morphisms.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3 and the paragraph after it ("Logic comorphisms are institution comorphisms with
signature and sentence translations that yield comorphisms between the entailment systems"). -/
structure CoHom (A : LogicalSystem.{u₁, v₁, w, m₁, m₂} Sign₁) (B : LogicalSystem.{u₂, v₂, w, m₁, m₂} Sign₂) where
  /-- The signature functor. -/
  Φ : Sign₁ ⥤ Sign₂
  /-- The corridors `I_A(Σ) → I_B(ΦΣ)`, natural in `Σ`. -/
  ρ : A.I ⟶ Φ ⋙ B.I
  /-- Sentence translation preserves derivability. -/
  map_derives : ∀ (S : Sign₁) (Γ : Set (A.I.obj S).Sen) (φ : (A.I.obj S).Sen), A.Derives S Γ φ →
    B.Derives (Φ.obj S) ((ρ.app S).sen '' Γ) ((ρ.app S).sen φ)

namespace CoHom

variable {A : LogicalSystem.{u₁, v₁, w, m₁, m₂} Sign₁} {B : LogicalSystem.{u₂, v₂, w, m₁, m₂} Sign₂}
  (f : CoHom A B)

/-- The underlying institution comorphism.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3. -/
def toInstCoHom : Inst.CoHom A.toInst B.toInst := ⟨f.Φ, f.ρ⟩

/-- The underlying entailment system comorphism `α : E_A ⟶ Φ ⋙ E_B`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3 (entailment system comorphisms). -/
def entailmentCoHom : A.entailmentSystem ⟶ f.Φ ⋙ B.entailmentSystem where
  app S := ⟨(f.ρ.app S).sen, fun h => f.map_derives S _ _ h⟩
  naturality _ _ σ := ER.hom_ext (congrArg Corridor.sen (f.ρ.naturality σ))

/-- A logic comorphism is conservative when its sentence translations reflect derivability.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.3, lifted to the indexed level in §4.1 ("easily lift from the non-indexed to the
indexed level"). -/
def Conservative : Prop :=
  ∀ (S : Sign₁) (Γ : Set (A.I.obj S).Sen) (φ : (A.I.obj S).Sen),
    B.Derives (f.Φ.obj S) ((f.ρ.app S).sen '' Γ) ((f.ρ.app S).sen φ) → A.Derives S Γ φ

/-- A logic comorphism is model-expansive when each model translation is surjective.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6, lifted to the indexed level in §4.1. -/
def ModelExpansive : Prop := ∀ S, Corridor.ModelExpansive (f.ρ.app S)

/-- Soundness is borrowed along model-expansive logic comorphisms: if `B` is sound then so
is `A`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7 (model-expansive corridors reflect semantic entailment), applied at each
signature. -/
theorem sound_of_sound (hexp : f.ModelExpansive) (hB : B.Sound) : A.Sound := by
  intro S Γ φ h
  exact (Corridor.entails_map_iff (f.ρ.app S) (hexp S) Γ φ).mpr
    (hB (f.Φ.obj S) _ _ (f.map_derives S Γ φ h))

end CoHom

end LogicalSystem

end Silmaril.Logic.Institution.Metatheory
