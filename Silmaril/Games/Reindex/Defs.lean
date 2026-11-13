module

public import Silmaril.Games.Institution.Defs

/-!
# Reindexing the institution of game semantics

A family of games indexed by a category `C` (a functor `Φ : C ⥤ Game`) gives an institution
`GInst.along Φ` with signatures `C`: the room at `X` is the `GInst` room of the game `Φ X`.

* `GInst.along Φ : Inst`, and the comorphism `GInst.alongCoHom Φ : along Φ → GInst` (signatures
  sent along `Φ`, identity corridors);
* `GInst.reindex F α : along Φ → along Ψ` for a functor `F : C ⥤ D` and a natural family of game
  morphisms `α : Φ ⟶ F ⋙ Ψ`. Its corridors are the `GInst` corridors of `α`: sentences are
  translated by `Game.senMap (α.app X)` and models are reducts along `α.app X`;
* `reindex_sat`: the satisfaction condition, which is that of `GInst`.

This is how a semantics that assigns a game to each of its points (a Wasm model, a scalar
instance, a component) maps into `GInst` (`docs/projects/spectec/README.md` §2).

New definitions.
-/

@[expose] public section

namespace Silmaril.Games.GInst

open CategoryTheory Silmaril.Logic.Institution

universe u v

/-- **`GInst` reindexed along a family of games** `Φ : C ⥤ Game`. -/
def along {C : Type u} [Category.{v} C] (Φ : C ⥤ Game.{0}) : Inst.{u, v, 0, 0, 0} where
  Sign := C
  I := Φ ⋙ GInst.institution

/-- The comorphism from a reindexed `GInst` into `GInst`. -/
def alongCoHom {C : Type u} [Category.{v} C] (Φ : C ⥤ Game.{0}) : Inst.CoHom (along Φ) GInst where
  Φ := Φ
  ρ := 𝟙 _

/-- **The comorphism of a natural family of game morphisms** `α : Φ ⟶ F ⋙ Ψ`: the corridor at
`X` is the `GInst` corridor of `α.app X`. -/
def reindex {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D] {Φ : C ⥤ Game.{0}}
    {Ψ : D ⥤ Game.{0}} (F : C ⥤ D) (α : Φ ⟶ F ⋙ Ψ) : Inst.CoHom (along Φ) (along Ψ) where
  Φ := F
  ρ := Functor.whiskerRight α GInst.institution ≫ (Functor.associator F Ψ GInst.institution).hom

/-- **The satisfaction condition of a reindexing**: a model of `Ψ (F X)` satisfies the
translation of `φ` iff its reduct along `α.app X` satisfies `φ`. -/
theorem reindex_sat {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {Φ : C ⥤ Game.{0}} {Ψ : D ⥤ Game.{0}} (F : C ⥤ D) (α : Φ ⟶ F ⋙ Ψ) (X : C)
    (σ : (Ψ.obj (F.obj X)).Model) (φ : GSen (Φ.obj X).E (Φ.obj X).F) :
    (Game.senMap (α.app X) φ).holds σ ↔ φ.holds (Game.reduct (α.app X) σ) :=
  Iff.rfl

end Silmaril.Games.GInst
