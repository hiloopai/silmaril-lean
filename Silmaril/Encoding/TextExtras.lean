module

public import Silmaril.Encoding.All

/-!
# Extras for layered (text) encodings

Additions to the generic encoding theory needed by the text formats
(S-expressions, WAT).  They are kept here rather than in the theory files so
that the theory branch stays independent.

* `F ⨾ E` — notation for `EncRel.comp F E`: spell `a` in an intermediate
  carrier with `E`, then spell that intermediate value with `F`.  (`F` is the
  *outer*, concrete layer: `sexpWat ⨾ watSyntax : EncRel String Module`.)
* Composition laws: associativity, identities (`EncRel.idRel`), monotonicity,
  interaction with `comap`/`map`/`push`/`pull`/`restrictCarrier`, and
  preservation of `Functional`/`Deterministic`.
* `EncCat.compFunctor F : EncCat τ ⥤ EncCat σ` — precomposition with an outer
  layer is a functor; the identity layer gives the identity functor and
  composite layers the composite functor up to natural isomorphism
  (`compFunctorIdIso`, `compFunctorCompIso`; the `…_obj` lemmas are the
  object-level equalities), and it commutes with carrier pushforward (on
  objects).
* `EncRel.Incomparable` — neither relation refines the other.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace EncRel

variable {σ σ' τ υ α β : Type}

/-- Relational composition of encoding layers: `(F ⨾ E) s a ↔ ∃ t, F s t ∧ E t a`. -/
infixr:80 " ⨾ " => EncRel.comp

/-- The identity layer: a carrier value spells exactly itself. -/
def idRel (σ : Type) : EncRel σ σ := fun s t => s = t

@[simp] theorem comp_apply (F : EncRel σ τ) (E : EncRel τ α) (s : σ) (a : α) :
    (F ⨾ E) s a ↔ ∃ t, F s t ∧ E t a := Iff.rfl

theorem comp_assoc (G : EncRel σ τ) (F : EncRel τ υ) (E : EncRel υ α) :
    (G ⨾ F) ⨾ E = G ⨾ (F ⨾ E) := by
  ext s a
  constructor
  · rintro ⟨u, ⟨t, hg, hf⟩, he⟩; exact ⟨t, hg, u, hf, he⟩
  · rintro ⟨t, hg, u, hf, he⟩; exact ⟨u, ⟨t, hg, hf⟩, he⟩

@[simp] theorem idRel_comp (E : EncRel σ α) : idRel σ ⨾ E = E := by
  ext s a
  constructor
  · rintro ⟨t, rfl, h⟩; exact h
  · intro h; exact ⟨s, rfl, h⟩

@[simp] theorem comp_idRel (E : EncRel σ α) : E ⨾ idRel α = E := by
  ext s a
  constructor
  · rintro ⟨t, h, rfl⟩; exact h
  · intro h; exact ⟨a, h, rfl⟩

theorem comp_mono {F F' : EncRel σ τ} {E E' : EncRel τ α} (hF : F ≤ F') (hE : E ≤ E') :
    F ⨾ E ≤ F' ⨾ E' := by
  rintro s a ⟨t, hf, he⟩
  exact ⟨t, hF _ _ hf, hE _ _ he⟩

theorem comp_mono_left {F F' : EncRel σ τ} (hF : F ≤ F') (E : EncRel τ α) :
    F ⨾ E ≤ F' ⨾ E := comp_mono hF le_rfl

theorem comp_mono_right (F : EncRel σ τ) {E E' : EncRel τ α} (hE : E ≤ E') :
    F ⨾ E ≤ F ⨾ E' := comp_mono le_rfl hE

/-- The inner layer may be reindexed before or after composing. -/
theorem comp_comap (F : EncRel σ τ) (f : β → α) (E : EncRel τ α) :
    F ⨾ comap f E = comap f (F ⨾ E) := rfl

theorem comp_map (F : EncRel σ τ) (f : α → β) (E : EncRel τ α) :
    F ⨾ map f E = map f (F ⨾ E) := by
  ext s b
  constructor
  · rintro ⟨t, hf, a, he, rfl⟩; exact ⟨a, ⟨t, hf, he⟩, rfl⟩
  · rintro ⟨a, ⟨t, hf, he⟩, rfl⟩; exact ⟨t, hf, a, he, rfl⟩

/-- Changing the outer carrier commutes with composition. -/
theorem push_comp (g : σ → σ') (F : EncRel σ τ) (E : EncRel τ α) :
    push g (F ⨾ E) = push g F ⨾ E := by
  ext s' a
  constructor
  · rintro ⟨s, rfl, t, hf, he⟩; exact ⟨t, ⟨s, rfl, hf⟩, he⟩
  · rintro ⟨t, ⟨s, rfl, hf⟩, he⟩; exact ⟨s, rfl, t, hf, he⟩

theorem pull_comp (g : σ' → σ) (F : EncRel σ τ) (E : EncRel τ α) :
    pull g (F ⨾ E) = pull g F ⨾ E := rfl

theorem restrictCarrier_comp (Q : σ → Prop) (F : EncRel σ τ) (E : EncRel τ α) :
    restrictCarrier (F ⨾ E) Q = restrictCarrier F Q ⨾ E := by
  ext s a
  constructor
  · rintro ⟨hq, t, hf, he⟩; exact ⟨t, ⟨hq, hf⟩, he⟩
  · rintro ⟨t, ⟨hq, hf⟩, he⟩; exact ⟨hq, t, hf, he⟩

/-- Meets distribute into the outer layer from above. -/
theorem inf_comp_le (F F' : EncRel σ τ) (E : EncRel τ α) :
    (F ⊓ F') ⨾ E ≤ (F ⨾ E) ⊓ (F' ⨾ E) := by
  rintro s a ⟨t, ⟨hf, hf'⟩, he⟩
  exact ⟨⟨t, hf, he⟩, ⟨t, hf', he⟩⟩

/-- Layering functional encodings is functional. -/
theorem Functional.comp {F : EncRel σ τ} {E : EncRel τ α} (hF : F.Functional)
    (hE : E.Functional) : (F ⨾ E).Functional := by
  rintro s a a' ⟨t, hf, he⟩ ⟨t', hf', he'⟩
  cases hF hf hf'
  exact hE he he'

/-- Layering deterministic encodings is deterministic. -/
theorem Deterministic.comp {F : EncRel σ τ} {E : EncRel τ α} (hF : F.Deterministic)
    (hE : E.Deterministic) : (F ⨾ E).Deterministic := by
  rintro s s' a ⟨t, hf, he⟩ ⟨t', hf', he'⟩
  cases hE he he'
  exact hF hf hf'

/-- A morphism of inner layers induces a morphism of the composites. -/
theorem Preserves.comp (F : EncRel σ τ) {E : EncRel τ α} {G : EncRel τ β} {f : α → β}
    (hf : Preserves E G f) : Preserves (F ⨾ E) (F ⨾ G) f := by
  rintro s a ⟨t, hF, hE⟩
  exact ⟨t, hF, hf _ _ hE⟩

/-- Neither encoding refines the other. -/
def Incomparable (E F : EncRel σ α) : Prop := ¬ E ≤ F ∧ ¬ F ≤ E

theorem Incomparable.symm {E F : EncRel σ α} (h : Incomparable E F) : Incomparable F E :=
  ⟨h.2, h.1⟩

/-- Two functional encodings that spell different values with the same carrier
value are incomparable (a single witness refutes both inclusions). -/
theorem incomparable_of_witness {E F : EncRel σ α} (hE : E.Functional) (hF : F.Functional)
    {s : σ} {a b : α} (ha : E s a) (hb : F s b) (hab : a ≠ b) : Incomparable E F := by
  refine ⟨fun h => hab (hF (h _ _ ha) hb), fun h => hab (hE ha (h _ _ hb))⟩

end EncRel

namespace EncCat

variable {σ σ' τ : Type}

/-- Precomposition with an outer layer `F : EncRel σ τ`: an encoding of `α` in
`τ` becomes an encoding of `α` in `σ`. -/
@[simps]
def compFunctor (F : EncRel σ τ) : EncCat τ ⥤ EncCat σ where
  obj X := ⟨X.ast, F ⨾ X.rel⟩
  map f := ⟨f.fn, EncRel.Preserves.comp F f.preserves⟩

/-- Composition with the identity layer is the identity functor on objects. -/
theorem compFunctor_idRel_obj (X : EncCat τ) : (compFunctor (EncRel.idRel τ)).obj X = X := by
  change (⟨X.ast, EncRel.idRel τ ⨾ X.rel⟩ : EncCat τ) = X
  rw [EncRel.idRel_comp]

/-- Composing layers composes the functors (on objects). -/
theorem compFunctor_comp_obj {υ : Type} (G : EncRel σ τ) (F : EncRel τ υ) (X : EncCat υ) :
    (compFunctor G).obj ((compFunctor F).obj X) = (compFunctor (G ⨾ F)).obj X := by
  change (⟨X.ast, G ⨾ (F ⨾ X.rel)⟩ : EncCat σ) = ⟨X.ast, (G ⨾ F) ⨾ X.rel⟩
  rw [EncRel.comp_assoc]

/-- Objects with equal encoding relations over the same syntax are isomorphic
(by the identity on syntax). -/
def isoOfRelEq {α : Type} {R R' : EncRel τ α} (h : R = R') :
    (⟨α, R⟩ : EncCat τ) ≅ ⟨α, R'⟩ where
  hom := ⟨id, fun _ _ ha => h ▸ ha⟩
  inv := ⟨id, fun _ _ ha => h ▸ ha⟩

/-- Composition with the identity layer is naturally isomorphic to the identity
functor. -/
def compFunctorIdIso : compFunctor (EncRel.idRel τ) ≅ 𝟭 (EncCat τ) :=
  NatIso.ofComponents (fun X => isoOfRelEq (EncRel.idRel_comp X.rel)) (fun _ => rfl)

/-- Composing layers composes the functors, up to natural isomorphism. -/
def compFunctorCompIso {υ : Type} (G : EncRel σ τ) (F : EncRel τ υ) :
    compFunctor F ⋙ compFunctor G ≅ compFunctor (G ⨾ F) :=
  NatIso.ofComponents (fun X => isoOfRelEq (EncRel.comp_assoc G F X.rel).symm) (fun _ => rfl)

/-- Pushing the composite along a carrier map is composing with the pushed
outer layer (e.g. UTF-8 bytes of WAT = UTF-8 bytes of S-expressions, then WAT
syntax). -/
theorem pushFunctor_compFunctor_obj (g : σ → σ') (F : EncRel σ τ) (X : EncCat τ) :
    (pushFunctor g).obj ((compFunctor F).obj X) = (compFunctor (F.push g)).obj X := by
  change (⟨X.ast, (F ⨾ X.rel).push g⟩ : EncCat σ') = ⟨X.ast, F.push g ⨾ X.rel⟩
  rw [EncRel.push_comp]

end EncCat

end Silmaril
