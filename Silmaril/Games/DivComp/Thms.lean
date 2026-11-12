module

public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.Composition.Thms
public import Mathlib.CategoryTheory.Category.Basic
import Silmaril.Proofs.Games.DivComp.Pos
import Silmaril.Proofs.Games.DivComp.Unit
import Silmaril.Proofs.Games.DivComp.Example
import Silmaril.Proofs.Games.DivComp.Assoc
import Silmaril.Proofs.Games.DivComp.Laws

/-!
# Composition of divergence-observing strategies: laws

* **Composition creates divergence from infinite hidden chatter**
  (`mem_div_comp_of_chatter`); chatter needs infinite plays of *both*
  components (`InfInteraction.chatter_inf`); the composite of two
  divergence-free strategies can diverge (`exists_divFree_comp_div`, with
  the server/client pair of `Silmaril.Proofs.Games.DivComp.Example`).
* Refinement is a precongruence (`comp_mono`).
* Copycat is a two-sided unit (`id_comp`, `comp_id`). The finite parts are
  `Strategy.id_comp`/`Strategy.comp_id`; divergence and infinite plays are
  handled in `Silmaril.Proofs.Games.DivComp.Unit`.
* `forget` preserves composition strictly (`forget_comp`, by definition) and
  copycat (`forget_id`); `ofStrategy` preserves composition
  (`ofStrategy_comp`) but not identities (copycat has infinite plays).
* **Composition is associative** (`comp_assoc`), including divergence and
  infinite plays, and signatures with divergence-observing strategies form a
  category (`DSig.category`, on the type synonym `DSig` so that it does not
  clash with the category of ordinary strategies). The proof
  (`Silmaril.Proofs.Games.DivComp.{ZipChain,Assoc}`) re-associates *increments*
  of increasing interactions: the increments of nested interactions interact
  (`zip_drop`), `Zip.assoc` is applied to increments only, and the results are
  concatenated, which yields increasing re-associated chains by dependent
  choice (`mergeA`, `mergeB`); an outer infinite interaction whose middle
  side stops growing turns into a divergence of the inner composite
  (`assembleA`, `assembleB`).
-/

public section

namespace Silmaril.Games.DStrategy

universe u

open Silmaril.Proofs.Games.DivComp

variable {E F G H : Sig.{u}}

/-! ## Membership -/

theorem mem_div_comp {σ : DStrategy E F} {τ : DStrategy F G} {p : List (Move E G)} :
    p ∈ (σ.comp τ).div ↔
      (∃ s t, Zip s t p ∧ ((s ∈ σ.div ∧ t ∈ τ.toStrategy) ∨ (s ∈ σ.toStrategy ∧ t ∈ τ.div))) ∨
      ∃ i : InfInteraction σ τ, ∀ n, i.p n = p := Iff.rfl

theorem mem_inf_comp {σ : DStrategy E F} {τ : DStrategy F G} {I : Set (List (Move E G))} :
    I ∈ (σ.comp τ).inf ↔ ∃ i : InfInteraction σ τ, i.p.Unbounded ∧ I = i.p.lim := Iff.rfl

/-! ## Composition creates divergence -/

/-- **Composition creates divergence from infinite hidden interaction.** An
infinite interaction of `σ` and `τ` whose visible part stays `p` makes the
composite diverge after `p`, whether or not `σ` or `τ` diverge. -/
theorem mem_div_comp_of_chatter {σ : DStrategy E F} {τ : DStrategy F G}
    (i : InfInteraction σ τ) {p : List (Move E G)} (hp : ∀ n, i.p n = p) :
    p ∈ (σ.comp τ).div :=
  .inr ⟨i, hp⟩

/-- Local divergence of the lower component propagates to the composite. -/
theorem mem_div_comp_of_left {σ : DStrategy E F} {τ : DStrategy F G} {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (hs : s ∈ σ.div) (ht : t ∈ τ.toStrategy)
    (hz : Zip s t p) : p ∈ (σ.comp τ).div :=
  .inl ⟨s, t, hz, .inl ⟨hs, ht⟩⟩

/-- Local divergence of the upper component propagates to the composite. -/
theorem mem_div_comp_of_right {σ : DStrategy E F} {τ : DStrategy F G} {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (hs : s ∈ σ.toStrategy) (ht : t ∈ τ.div)
    (hz : Zip s t p) : p ∈ (σ.comp τ).div :=
  .inl ⟨s, t, hz, .inr ⟨hs, ht⟩⟩

/-- An infinite interaction moves forever on at least one side. -/
theorem InfInteraction.unbounded_or {σ : DStrategy E F} {τ : DStrategy F G}
    (i : InfInteraction σ τ) : i.s.Unbounded ∨ i.t.Unbounded :=
  Laws.unbounded_or i

/-- **Chatter is infinite on both sides.** In an infinite interaction whose
visible part stays `p`, both components make infinitely many moves at the
hidden interface; so both play one of their infinite plays. -/
theorem InfInteraction.chatter_inf {σ : DStrategy E F} {τ : DStrategy F G}
    (i : InfInteraction σ τ) {p : List (Move E G)} (hp : ∀ n, i.p n = p) :
    i.s.Unbounded ∧ i.t.Unbounded ∧ i.s.lim ∈ σ.inf ∧ i.t.lim ∈ τ.inf := by
  obtain ⟨hs, ht⟩ : i.s.Unbounded ∧ i.t.Unbounded :=
    Silmaril.Proofs.Games.DivComp.chatter_unbounded i hp
  exact ⟨hs, ht, i.lim_s hs, i.lim_t ht⟩

/-- **Divergence-free components can compose to a diverging one.** There are
two strategies of the divergence-free reading `limits ⊤` (all legal plays and
all infinite legal plays, no divergence) whose composite diverges: a server
answering every call at once and a client calling it forever. -/
theorem exists_divFree_comp_div : ∃ (F : Sig.{0}) (σ : DStrategy Sig.empty F)
    (τ : DStrategy F F), σ = limits ⊤ ∧ τ = limits ⊤ ∧ σ.div = ∅ ∧ τ.div = ∅ ∧
      (σ.comp τ).div.Nonempty :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, ⟨_, Silmaril.Proofs.Games.DivComp.Example.comp_div⟩⟩

/-! ## Monotonicity -/

/-- Refinement is a precongruence for composition. -/
theorem comp_mono {σ σ' : DStrategy E F} {τ τ' : DStrategy F G} (hσ : σ ≤ σ') (hτ : τ ≤ τ') :
    σ.comp τ ≤ σ'.comp τ' :=
  Laws.comp_mono hσ hτ

theorem comp_mono_left {σ σ' : DStrategy E F} (h : σ ≤ σ') (τ : DStrategy F G) :
    σ.comp τ ≤ σ'.comp τ :=
  comp_mono h le_rfl

theorem comp_mono_right (σ : DStrategy E F) {τ τ' : DStrategy F G} (h : τ ≤ τ') :
    σ.comp τ ≤ σ.comp τ' :=
  comp_mono le_rfl h

/-! ## Units -/

/-- Copycat is a left unit. -/
theorem id_comp (δ : DStrategy E F) : (DStrategy.id E).comp δ = δ :=
  ext (Strategy.id_comp δ.toStrategy) (IdComp.div_subset.antisymm IdComp.subset_div)
    (IdComp.inf_subset.antisymm IdComp.subset_inf)

/-- Copycat is a right unit. -/
theorem comp_id (δ : DStrategy E F) : δ.comp (DStrategy.id F) = δ :=
  ext (Strategy.comp_id δ.toStrategy) (CompId.div_subset.antisymm CompId.subset_div)
    (CompId.inf_subset.antisymm CompId.subset_inf)

/-! ## Embeddings -/

/-- The least reading preserves composition: strategies without infinite plays
cannot chatter forever. -/
theorem ofStrategy_comp (σ : Strategy E F) (τ : Strategy F G) :
    (ofStrategy σ).comp (ofStrategy τ) = ofStrategy (σ.comp τ) :=
  Laws.ofStrategy_comp σ τ

/-! ## Associativity -/

/-- Associativity of the finite-play component. -/
theorem forget_comp_assoc (σ : DStrategy E F) (τ : DStrategy F G) (ρ : DStrategy G H) :
    ((σ.comp τ).comp ρ).forget = (σ.comp (τ.comp ρ)).forget :=
  Strategy.comp_assoc _ _ _

/-- **Composition is associative**, for finite plays, divergence and infinite
plays. -/
theorem comp_assoc (σ : DStrategy E F) (τ : DStrategy F G) (ρ : DStrategy G H) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) :=
  ext (Strategy.comp_assoc _ _ _)
    (Silmaril.Proofs.Games.DivComp.div_assoc_le.antisymm Silmaril.Proofs.Games.DivComp.div_le_assoc)
    (Silmaril.Proofs.Games.DivComp.inf_assoc_le.antisymm Silmaril.Proofs.Games.DivComp.inf_le_assoc)

/-- Signatures, as objects of the category of divergence-observing strategies
(a type synonym, so that this category does not clash with the category
`Silmaril.Games.Category` of ordinary strategies). -/
@[expose] def _root_.Silmaril.Games.DSig : Type (u + 1) := Sig.{u}

/-- Signatures and divergence-observing strategies form a category: morphisms
`E ⟶ F` are `DStrategy E F`, identities are copycat and `σ ≫ τ = σ.comp τ`. -/
instance _root_.Silmaril.Games.DSig.category : CategoryTheory.Category DSig.{u} where
  Hom E F := DStrategy E F
  id E := DStrategy.id E
  comp σ τ := σ.comp τ
  id_comp := id_comp
  comp_id := comp_id
  assoc := comp_assoc

open CategoryTheory in
/-- Morphisms of `DSig` are divergence-observing strategies. -/
theorem _root_.Silmaril.Games.DSig.hom_def (E F : DSig.{u}) :
    (E ⟶ F) = DStrategy (E : Sig.{u}) (F : Sig.{u}) := rfl

open CategoryTheory in
/-- Composition in `DSig` is `DStrategy.comp`. -/
theorem _root_.Silmaril.Games.DSig.comp_def {E F G : DSig.{u}} (σ : E ⟶ F) (τ : F ⟶ G) :
    σ ≫ τ = DStrategy.comp (E := (E : Sig.{u})) (F := (F : Sig.{u})) (G := (G : Sig.{u})) σ τ :=
  rfl

end Silmaril.Games.DStrategy
