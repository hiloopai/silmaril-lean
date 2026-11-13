module

public import Silmaril.Games.Composition.Thms
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of signatures and strategies

Objects are effect signatures, morphisms `E ⟶ F` are strategies
`Strategy E F` (components implementing `F` on top of `E`), identities are
copycat and `σ ≫ τ = σ.comp τ`. Each hom-set is a complete lattice under
refinement and composition is monotone (`Strategy.comp_mono`).

This is the single-threaded, angelic analogue of Koenig and Shao's category
`G_ib` (LICS 2020, Def. 3.7).
-/

@[expose] public section

namespace Silmaril.Games

universe u

open CategoryTheory

/-- Signatures and strategies form a category. -/
instance : Category Sig.{u} where
  Hom E F := Strategy E F
  id E := Strategy.id E
  comp σ τ := σ.comp τ
  id_comp := Strategy.id_comp
  comp_id := Strategy.comp_id
  assoc := Strategy.comp_assoc

/-- Morphisms are strategies. -/
theorem Category.hom_def (E F : Sig.{u}) : (E ⟶ F) = Strategy E F := rfl

/-- Identities are copycat. -/
theorem Category.id_def (E : Sig.{u}) : 𝟙 E = Strategy.id E := rfl

/-- Composition is `Strategy.comp`, in diagrammatic order. -/
theorem Category.comp_def {E F G : Sig.{u}} (σ : E ⟶ F) (τ : F ⟶ G) :
    σ ≫ τ = Strategy.comp σ τ := rfl

end Silmaril.Games
