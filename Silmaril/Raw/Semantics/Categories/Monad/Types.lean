module

public import Silmaril.Raw.Semantics.Categories.Monad.Kleisli
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

@[expose] public section

/-! # Every lawful monad on `Type` is strong -/

universe u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- The canonical tensorial strength of a monad on types. -/
def typeMonadStrength (X Y : Type u) : X × m Y → m (X × Y) :=
  fun p ↦ (fun y ↦ (p.1, y)) <$> p.2

instance ofTypeMonadStrong : (ofTypeMonad m).Strong where
  strength X Y := ↾(typeMonadStrength m X Y)
  naturality_left f Y := by
    ext p
    dsimp [ofTypeMonad, ofTypeFunctor] at p
    change (fun y ↦ (f p.1, y)) <$> p.2 =
      (fun q ↦ (f q.1, q.2)) <$> ((fun y ↦ (p.1, y)) <$> p.2)
    simp
  naturality_right := fun X {_ _} f ↦ by
    ext p
    dsimp [ofTypeMonad, ofTypeFunctor] at p
    change (fun y ↦ (p.1, y)) <$> (f <$> p.2) =
      (fun q ↦ (q.1, f q.2)) <$> ((fun y ↦ (p.1, y)) <$> p.2)
    simp
  associativity X Y Z := by
    ext p
    dsimp [ofTypeMonad, ofTypeFunctor] at p
    change (fun yz ↦ (p.1.1, yz)) <$> ((fun z ↦ (p.1.2, z)) <$> p.2) =
      (fun q ↦ (q.1.1, (q.1.2, q.2))) <$> ((fun z ↦ (p.1, z)) <$> p.2)
    simp
  left_unitality X := by
    ext p
    dsimp [ofTypeMonad, ofTypeFunctor] at p
    change (fun q : PUnit × X ↦ q.2) <$> ((fun y ↦ (p.1, y)) <$> p.2) = p.2
    simp
  unit X Y := by
    ext p
    dsimp [ofTypeMonad, ofTypeFunctor] at p
    change (fun y ↦ (p.1, y)) <$> pure p.2 = (pure p : m _)
    simp
  multiplication X Y := by
    ext p
    dsimp [ofTypeMonad, ofTypeFunctor] at p
    change (fun y ↦ (p.1, y)) <$> joinM p.2 =
      joinM ((fun q ↦ (fun y ↦ (q.1, y)) <$> q.2) <$>
        ((fun my ↦ (p.1, my)) <$> p.2))
    simp [joinM]

@[simp] theorem ofTypeMonad_strength_apply (X Y : Type u) (p : X × m Y) :
    Monad.Strong.strength (T := ofTypeMonad m) X Y p = typeMonadStrength m X Y p := rfl

/-- Kleisli arrows of every lawful monad on `Type` form a premonoidal category. -/
@[reducible] def typeMonadKleisliPremonoidal :
    PremonoidalCategory (Kleisli (ofTypeMonad m)) := inferInstance

/-- Kleisli arrows of every lawful monad on `Type`, together with pure functions, form a Freyd
category. -/
@[reducible] def typeMonadKleisliFreyd :
    FreydCategory (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) := inferInstance

end CategoryTheory
