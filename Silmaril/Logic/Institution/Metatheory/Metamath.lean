module

public import Silmaril.Logic.Institution.Metatheory.Entailment
public import Silmaril.Logic.Metamath.Category.Basic
public import Silmaril.Logic.Metamath.Category.Lattice
public import Silmaril.Logic.Metamath.SetMM.Consistency
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# Metamath databases as an entailment system

The tree level of `Silmaril.Logic.Metamath` packaged in the sense of
Mossakowski–Diaconescu–Tarlecki:

* **Signatures** `MMSig`: Metamath grammars (rule labels, constants, an infinite type of
  variables and a `Grammar`). **Signature morphisms** are the syntax rewrites
  `Grammar.Rewrite` (derived signature morphisms: a typecode map, an injective variable
  renaming and a template for each syntax rule); `Rewrite.id`, `Rewrite.comp` and their laws
  make `MMSig` a category.
* **Sentences**: well-formed tree assertions `Grammar.TWFAssertion G` (a frame: disjoint
  variable conditions, floating and essential hypotheses, conclusion).
* **Entailment** `Γ ⊢ A`: `Grammar.TDerivable G Γ A`, Metamath's tree derivability from the
  axioms `Γ`. It is Tarskian (`Grammar.TDerivable.of_mem`, `.mono`, `.trans`, the last by cut
  admissibility, which needs infinitely many variables), and rewrites preserve it
  (`Grammar.TDerivable.rewrite`). This is the entailment system `Metamath.entailment : MMSig ⥤ ER`.
* **Models**: Carneiro's models of a grammar (`Metamath.Model`), with satisfaction
  `Model.Satisfies`; at each grammar this is the room `Metamath.room G`. Soundness of the logic
  room (`Metamath.sound`) is `Metamath.Model.sound`.
* `GAxSet` (grammatical axiom sets) are presentations `(G, Γ)` in this entailment system, and
  `GAxSet` morphisms are the rewrites that are presentation morphisms
  (`Metamath.gaxSetHom_iff`, from `GAxSet.Hom.map_derivable_iff`).
* The ZFSet model of set.mm's `ZFC` is soundness of the presentation `(set.mm, ZFC)` in the
  model `SetMM.model ZFSet N` (`Metamath.zfc_sound`, equivalent to `SetMM.sound_zfc`).

The model functor of a Metamath institution (algebra reducts along rewrites, which interpret
each rule by its template) is not constructed here; see `docs/projects/logic.md`.
-/

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory Silmaril.Logic.Metamath Silmaril.Logic.Metamath.Grammar

universe u w

/-- A Metamath signature: a grammar over an infinite type of variables. -/
structure MMSig : Type (u + 1) where
  /-- Syntax rule labels. -/
  L : Type u
  /-- Constants (including typecodes). -/
  C : Type u
  /-- Variables. -/
  V : Type u
  [decEq : DecidableEq V]
  [infinite : Infinite V]
  /-- The grammar. -/
  G : Grammar L C V

attribute [instance] MMSig.decEq MMSig.infinite

namespace MMSig

/-- Metamath grammars and syntax rewrites form a category.

Source: the laws `Grammar.Rewrite.id_comp`, `Grammar.Rewrite.comp_id`,
`Grammar.Rewrite.comp_assoc` (`docs/projects/metamath.md`); signature morphisms in the sense of
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.1. -/
instance category : Category.{u} MMSig.{u} where
  Hom X Y := Rewrite X.G Y.G
  id X := Rewrite.id X.G
  comp f g := f.comp g
  id_comp f := Rewrite.id_comp f
  comp_id f := Rewrite.comp_id f
  assoc f g h := Rewrite.comp_assoc f g h

end MMSig

namespace Metamath

/-- Metamath tree derivability as an entailment relation on well-formed assertions.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.1; derivability is `Silmaril.Logic.Metamath.Grammar.TDerivable`. -/
def er (X : MMSig.{u}) : ER.{u} where
  Sen := TWFAssertion X.G
  Derives Γ A := TDerivable X.G (Subtype.val '' Γ) A.1
  refl A := TDerivable.of_mem ⟨A, Set.mem_singleton A, rfl⟩ A.2
  mono := fun h hA => hA.mono (Set.image_mono h)
  trans := fun {Γ Δ _} hΔ hψ => TDerivable.trans (Δ := Subtype.val '' (Γ ∪ Δ)) (by
    rintro _ ⟨φ, hφ | hφ, rfl⟩
    · exact TDerivable.of_mem ⟨φ, hφ, rfl⟩ φ.2
    · exact hΔ φ hφ) hψ

/-- Translation of well-formed assertions along a rewrite. -/
def senMap {X Y : MMSig.{u}} (f : X ⟶ Y) (A : TWFAssertion X.G) : TWFAssertion Y.G :=
  ⟨Rewrite.assertion f A.1, Rewrite.wellFormed (f := f) A.2⟩

/-- Rewrites preserve derivability (`Grammar.TDerivable.rewrite`). -/
theorem senMap_derives {X Y : MMSig.{u}} (f : X ⟶ Y) {Γ : Set (TWFAssertion X.G)}
    {A : TWFAssertion X.G} (h : (er X).Derives Γ A) :
    (er Y).Derives (senMap f '' Γ) (senMap f A) := by
  have e : Subtype.val '' (senMap f '' Γ) = Rewrite.assertion f '' (Subtype.val '' Γ) := by
    rw [Set.image_image, Set.image_image]; rfl
  show TDerivable Y.G (Subtype.val '' (senMap f '' Γ)) (Rewrite.assertion f A.1)
  rw [e]
  exact TDerivable.rewrite (f : Rewrite X.G Y.G)
    (by rintro _ ⟨B, -, rfl⟩; exact B.2) A.2 h

/-- **Metamath as an entailment system**, `MMSig ⥤ ER`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.1. -/
def entailment : MMSig.{u} ⥤ ER.{u} where
  obj := er
  map f := ⟨senMap f, senMap_derives f⟩
  map_id _ := ER.hom_ext (funext fun A => Subtype.ext (Rewrite.id_assertion A.2))
  map_comp f g := ER.hom_ext (funext fun A => Subtype.ext (Rewrite.comp_assertion f g A.2))

/-- The room of a grammar: well-formed assertions, Carneiro's models (as a discrete category)
and `M ⊨ A ↔ M.Satisfies A`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.1; models and satisfaction are `Silmaril.Logic.Metamath.Model` and
`Model.Satisfies` (Carneiro, *Models for Metamath*, Definition 10). -/
def room (X : MMSig.{u}) : Room.{u, max u (w + 1), max u (w + 1)} where
  Sen := TWFAssertion X.G
  Mod := Cat.of (Discrete (Model.{u, w} X.G))
  Sat M A := Model.Satisfies (Discrete.as M) A.1

/-- **Soundness of the Metamath logic room**: `Γ ⊢ A` implies `Γ ⊨ A`. Derived from
`Silmaril.Logic.Metamath.Model.sound` (Carneiro, *Models for Metamath*, Theorem 1).

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.3 (sound logic rooms). -/
theorem sound (X : MMSig.{u}) : (room.{u, w} X).IsSound (er X).Derives := by
  intro Γ A h M hM
  exact Model.sound (Discrete.as M) (by rintro _ ⟨B, -, rfl⟩; exact B.2)
    (by rintro _ ⟨B, hB, rfl⟩; exact hM B hB) h

/-! ### Grammatical axiom sets as presentations -/

/-- The signature of a grammatical axiom set with infinitely many variables. -/
def ofGAxSet (X : GAxSet.{u}) [Infinite X.V] : MMSig.{u} := ⟨X.L, X.C, X.V, X.G⟩

/-- The axioms of a grammatical axiom set, as sentences of its signature. -/
def axiomsOf (X : GAxSet.{u}) : Set (TWFAssertion X.G) := {A | A.1 ∈ X.axioms}

theorem val_image_axiomsOf (X : GAxSet.{u}) : Subtype.val '' axiomsOf X = X.axioms := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact hB
  · intro hA
    exact ⟨⟨A, X.wf A hA⟩, hA, rfl⟩

/-- **`GAxSet` morphisms are presentation morphisms.** A rewrite underlies a morphism of
grammatical axiom sets `X ⟶ Y` iff it sends every axiom of `X` to a consequence of the axioms
of `Y` in the entailment system `Metamath.entailment`. Derived from
`GAxSet.Hom.map_derivable_iff`.

Source: `goguen-burstall-1992` in `references.bib`, §2.2, Definition 5
(theory morphisms) and §2.3, Lemma 8 (presentation lemma: it suffices to send axioms into the
closure of the target), with entailment in place of semantic closure as in `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`,
§4, Definition 4.1. -/
theorem gaxSetHom_iff (X Y : GAxSet.{u}) [Infinite X.V] [Infinite Y.V]
    (f : ofGAxSet X ⟶ ofGAxSet Y) :
    (∃ g : X ⟶ Y, g.toRewrite = f) ↔
      ∀ A ∈ axiomsOf X, (er (ofGAxSet Y)).Derives (axiomsOf Y) (senMap f A) := by
  constructor
  · rintro ⟨g, rfl⟩ A hA
    show TDerivable Y.G (Subtype.val '' axiomsOf Y) (Rewrite.assertion g.toRewrite A.1)
    rw [val_image_axiomsOf]
    exact g.derivable_axiom hA
  · intro h
    refine ⟨GAxSet.Hom.ofAxioms (X := X) (Y := Y) f fun A hA => ?_, rfl⟩
    have h' := h ⟨A, X.wf A hA⟩ hA
    change TDerivable Y.G (Subtype.val '' axiomsOf Y) _ at h'
    rwa [val_image_axiomsOf] at h'

/-! ### The ZFSet model of set.mm's ZFC -/

/-- set.mm's grammar as a Metamath signature. -/
def setMM : MMSig.{0} := ⟨SetMM.L, String, String, SetMM.grammar⟩

/-- set.mm's `ZFC`, as sentences of `setMM`. -/
def zfc : Set (TWFAssertion SetMM.grammar) := {A | A.1 ∈ SetMM.zfc}

/-- Entailment from `Metamath.zfc` is tree derivability from `SetMM.zfc`. -/
theorem derives_zfc_iff (A : TWFAssertion SetMM.grammar) :
    (er setMM).Derives zfc A ↔ TDerivable SetMM.grammar SetMM.zfc A.1 := by
  have e : Subtype.val '' zfc = SetMM.zfc := by
    ext B
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact hB
    · intro hB
      exact ⟨⟨B, SetMM.wellFormed_zfc B hB⟩, hB, rfl⟩
  show TDerivable SetMM.grammar (Subtype.val '' zfc) A.1 ↔ _
  rw [e]

/-- **The ZFSet model edge as soundness.** Every consequence of `ZFC` in the entailment system
`Metamath.entailment` holds in the ZFSet model `SetMM.model ZFSet N`. Derived from
`SetMM.sound_zfc`, to which it is equivalent by `derives_zfc_iff`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.3 (soundness, here for the single model `ZFSet`); the original theorem is
`Silmaril.Logic.Metamath.SetMM.sound_zfc` (`docs/projects/metamath.md`). -/
theorem zfc_sound {N : Type (u + 1)} [DecidableEq N] [Infinite N] (A : TWFAssertion SetMM.grammar)
    (h : (er setMM).Derives zfc A) : (SetMM.model ZFSet.{u} N).Satisfies A.1 :=
  SetMM.sound_zfc ((derives_zfc_iff A).mp h)

/-- The ZFSet model edge, stated as satisfaction of `ZFC` in the room of `setMM`: the ZFSet
model is a model of the presentation `(setMM, zfc)`. Derived from `SetMM.isModel_zfc`. -/
theorem zfSet_mem_modelsOf {N : Type (u + 1)} [DecidableEq N] [Infinite N] :
    ∀ A ∈ zfc, (SetMM.model ZFSet.{u} N).Satisfies A.1 :=
  fun _ hA => SetMM.isModel_zfc _ hA

end Metamath

end Silmaril.Logic.Institution.Metatheory
