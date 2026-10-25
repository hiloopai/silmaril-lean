module

public import Silmaril.Compile.Category.Language
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Calling and simulation conventions

A *convention* `c : L ⟶ L'` between languages fixes how source interfaces are realised in the
target (`Φ`, the interface/ABI translation) and how target observations correspond to source
observations (`R`, a relation `L.Obs → L'.Obs → Prop`). This is the behaviour-level shadow of a
CompCertO simulation convention (Koenig and Shao (2021), *CompCertO* (see references.bib),
Definition 2.6, p. 4; refinement of conventions is Definition 5.1, p. 12), with the Kripke
world structure collapsed into the relation.

Conventions compose (`Φ` by composition, `R` by relational composition), so languages and
conventions form a category; the identity convention has `R = Eq`. Conventions are ordered:
`c ≤ d` when they agree on interfaces and `c.R ⊆ d.R` (`d` admits more target behaviours).

Each convention induces the sentence translation `α = c.lift` (the existential image of a
specification). When the convention is a *read-back* (`R o o' ↔ o = g o'` for a function
`g : L'.Obs → L.Obs` reading target observations back as source observations) it also has the
model translation `β = g ''`. These are the data for a read-back construction
in institution theory. A general institution/comorphism API and its
correspondence theorem are not included in this public closure.

## Main definitions

* `Convention L L'`, the category instance on `Language` (objects: languages; morphisms:
  conventions), the partial order on conventions.
* `Convention.lift`: `α`, translation of specifications (and behaviour sets) through `c`.
* `Convention.ReadBack`: conventions determined by a target-to-source observation function.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

/-- A convention between two languages: interface translation and observation matching.

Source: Koenig and Shao (2021), *CompCertO* (see references.bib), Definition 2.6, p. 4
(simulation conventions; here without Kripke worlds). -/
@[ext]
structure Convention (L L' : Language.{u}) : Type u where
  /-- Interface (ABI) translation. -/
  Φ : L.Iface → L'.Iface
  /-- Observation matching: `R o o'` when target observation `o'` realises source `o`. -/
  R : L.Obs → L'.Obs → Prop

namespace Convention

/-- The identity convention. -/
def id (L : Language.{u}) : Convention L L := ⟨_root_.id, (· = ·)⟩

/-- Composition of conventions.

Source: Koenig and Shao (2021), *CompCertO* (see references.bib), Definition 3.6, p. 8
(composition of simulation conventions). -/
def comp {L₁ L₂ L₃ : Language.{u}} (c : Convention L₁ L₂) (d : Convention L₂ L₃) :
    Convention L₁ L₃ :=
  ⟨d.Φ ∘ c.Φ, Relation.Comp c.R d.R⟩

end Convention

/-- Languages and conventions form a category. -/
instance Language.category : Category.{u} Language.{u} where
  Hom := Convention
  id := Convention.id
  comp := Convention.comp
  id_comp _ := Convention.ext rfl Relation.eq_comp
  comp_id _ := Convention.ext rfl Relation.comp_eq
  assoc _ _ _ := Convention.ext rfl Relation.comp_assoc

namespace Convention

variable {L L' L'' : Language.{u}}

@[simp] theorem id_Φ (L : Language.{u}) : (𝟙 L : Convention L L).Φ = _root_.id := rfl
@[simp] theorem id_R (L : Language.{u}) : (𝟙 L : Convention L L).R = (· = ·) := rfl
@[simp] theorem comp_Φ (c : L ⟶ L') (d : L' ⟶ L'') : (c ≫ d).Φ = d.Φ ∘ c.Φ := rfl
@[simp] theorem comp_R (c : L ⟶ L') (d : L' ⟶ L'') : (c ≫ d).R = Relation.Comp c.R d.R := rfl

/-- Conventions are ordered by inclusion of observation matchings, at a fixed interface map. -/
instance : PartialOrder (Convention L L') where
  le c d := c.Φ = d.Φ ∧ c.R ≤ d.R
  le_refl c := ⟨rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := Convention.ext h₁.1 (le_antisymm h₁.2 h₂.2)

/-- The same order on morphisms of `Language`. -/
instance : PartialOrder (L ⟶ L') := inferInstanceAs (PartialOrder (Convention L L'))

theorem le_def {c d : Convention L L'} : c ≤ d ↔ c.Φ = d.Φ ∧ c.R ≤ d.R := Iff.rfl

theorem hom_le_def {c d : L ⟶ L'} : c ≤ d ↔ c.Φ = d.Φ ∧ c.R ≤ d.R := Iff.rfl

/-- Composition of conventions is monotone in both arguments (poset enrichment). -/
theorem comp_mono {c c' : L ⟶ L'} {d d' : L' ⟶ L''} (hc : c ≤ c') (hd : d ≤ d') :
    c ≫ d ≤ c' ≫ d' := by
  refine ⟨by rw [comp_Φ, comp_Φ, hc.1, hd.1], ?_⟩
  rintro a b ⟨x, hx, hy⟩
  exact ⟨x, hc.2 _ _ hx, hd.2 _ _ hy⟩

/-! ### Translation of specifications -/

/-- The translation `α` of a specification (or a behaviour set) through a convention: the target
observations that realise some source observation in `B`. -/
def lift (c : Convention L L') (B : Set L.Obs) : Set L'.Obs := {o' | ∃ o ∈ B, c.R o o'}

theorem lift_mono (c : Convention L L') : Monotone c.lift := by
  rintro B B' hB o' ⟨o, ho, h⟩
  exact ⟨o, hB ho, h⟩

theorem lift_id (B : Set L.Obs) : (𝟙 L : Convention L L).lift B = B := by
  ext o
  exact ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨o, h, rfl⟩⟩

theorem lift_comp (c : L ⟶ L') (d : L' ⟶ L'') (B : Set L.Obs) :
    (c ≫ d).lift B = d.lift (c.lift B) := by
  ext o''
  constructor
  · rintro ⟨o, ho, o', h₁, h₂⟩
    exact ⟨o', ⟨o, ho, h₁⟩, h₂⟩
  · rintro ⟨o', ⟨o, ho, h₁⟩, h₂⟩
    exact ⟨o, ho, o', h₁, h₂⟩

theorem lift_le_of_le {c d : Convention L L'} (h : c ≤ d) (B : Set L.Obs) :
    c.lift B ⊆ d.lift B := by
  rintro o' ⟨o, ho, hr⟩
  exact ⟨o, ho, h.2 _ _ hr⟩

/-! ### Read-back conventions and comorphisms -/

/-- A read-back convention: every target observation is read back as exactly one source
observation, `R o o' ↔ o = g o'`. This is the condition under which the convention is an
institution comorphism of behavioural institutions. -/
structure ReadBack (c : Convention L L') where
  /-- Reading target observations back as source observations. -/
  g : L'.Obs → L.Obs
  /-- The matching relation is the converse graph of `g`. -/
  spec : ∀ o o', c.R o o' ↔ o = g o'

/-- The identity convention reads back by the identity. -/
def ReadBack.id (L : Language.{u}) : ReadBack (𝟙 L) := ⟨_root_.id, fun _ _ => Iff.rfl⟩

/-- Read-backs compose. -/
def ReadBack.comp {c : L ⟶ L'} {d : L' ⟶ L''} (hc : ReadBack c) (hd : ReadBack d) :
    ReadBack (c ≫ d) :=
  ⟨hc.g ∘ hd.g, fun o o'' => by
    simp only [comp_R, Relation.Comp, hc.spec, hd.spec, Function.comp_apply]
    exact ⟨fun ⟨_, h₁, h₂⟩ => h₂ ▸ h₁, fun h => ⟨_, h, rfl⟩⟩⟩

theorem ReadBack.lift_eq {c : Convention L L'} (h : ReadBack c) (B : Set L.Obs) :
    c.lift B = h.g ⁻¹' B := by
  ext o'
  simp only [lift, h.spec, Set.mem_preimage]
  exact ⟨fun ⟨_, hB, e⟩ => e ▸ hB, fun hB => ⟨_, hB, rfl⟩⟩

/-- The comorphism satisfaction condition as an inclusion statement (helper for `corridor`). -/
theorem ReadBack.subset_lift_iff {c : Convention L L'} (h : ReadBack c) (B' : Set L'.Obs)
    (φ : Set L.Obs) : B' ⊆ c.lift φ ↔ h.g '' B' ⊆ φ := by
  rw [h.lift_eq, Set.image_subset_iff]

/-- The comorphism satisfaction condition for behaviour models of programs:
`beh p' ⊆ α φ ↔ g '' beh p' ⊆ φ`. -/
theorem ReadBack.sat_iff {c : Convention L L'} (h : ReadBack c) (B' : Set L'.Obs)
    (φ : Set L.Obs) : B' ⊆ c.lift φ ↔ h.g '' B' ⊆ φ :=
  h.subset_lift_iff B' φ

end Convention

end Silmaril.Compile.Category
