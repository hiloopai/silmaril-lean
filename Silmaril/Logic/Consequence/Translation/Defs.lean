module

public import Silmaril.Logic.Consequence.Defs
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Translations between consequence systems

A *(sound) translation* `S ⟶ T` from `S : System Ax C` to `T : System Ax' C'` maps contexts
`ax : Ax → Ax'` and conclusions `c : C → C'` so that every `S`-judgement is sent to a
`T`-judgement: `S ≤ T.pullback ax c`. A translation is *conservative* when it also reflects
judgements: `T.pullback ax c ≤ S`.

* `Translation S T`, with `Translation.id`, `Translation.comp`, and `Translation.ofLE`
  (inclusion `S ≤ T` as a translation with identity maps).
* `Sys`: systems bundled with their context and conclusion types; `Sys.category` is the
  category of systems and translations (Mathlib's `Category`). The laws hold by `rfl` up to
  `Translation.ext`, since translations are determined by their maps
  (`Silmaril.Logic.Consequence.Translation.Thms`).
* Witness translations `WTranslation W V` map witnesses along the same pair of maps; `WSys` is
  their category, and erasure is a functor `WSys.erase : WSys ⥤ Sys`.
-/

@[expose] public section

namespace Silmaril.Consequence

open CategoryTheory

universe u v w u' v' w' u'' v'' w''

/-- A sound translation from `S` to `T`: maps of contexts and conclusions sending every
`S`-judgement to a `T`-judgement. -/
structure Translation {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'}
    (S : System Ax C) (T : System Ax' C') where
  /-- The map of contexts. -/
  ax : Ax → Ax'
  /-- The map of conclusions. -/
  c : C → C'
  /-- Soundness: `a ⊢_S φ` implies `ax a ⊢_T c φ`. -/
  sound : S ≤ T.pullback ax c

namespace Translation

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'} {Ax'' : Type u''}
  {C'' : Type v''}

@[ext]
theorem ext {S : System Ax C} {T : System Ax' C'} {f g : Translation S T} (h₁ : f.ax = g.ax)
    (h₂ : f.c = g.c) : f = g := by
  cases f; cases g; cases h₁; cases h₂; rfl

/-- The identity translation. -/
def id (S : System Ax C) : Translation S S := ⟨fun a => a, fun c => c, fun _ _ h => h⟩

/-- Composition of translations (diagrammatic order: first `f`, then `g`). -/
def comp {S : System Ax C} {T : System Ax' C'} {U : System Ax'' C''} (f : Translation S T)
    (g : Translation T U) : Translation S U :=
  ⟨g.ax ∘ f.ax, g.c ∘ f.c, fun a φ h => g.sound _ _ (f.sound a φ h)⟩

/-- An inclusion `S ≤ T` of systems over the same types, as a translation with identity maps. -/
def ofLE {S T : System Ax C} (h : S ≤ T) : Translation S T := ⟨fun a => a, fun c => c, h⟩

/-- `f` is conservative: it reflects judgements as well as preserving them. -/
def Conservative {S : System Ax C} {T : System Ax' C'} (f : Translation S T) : Prop :=
  T.pullback f.ax f.c ≤ S

end Translation

/-- A consequence system bundled with its context and conclusion types. -/
structure Sys : Type (max (u + 1) (v + 1)) where
  /-- The contexts. -/
  Ax : Type u
  /-- The conclusions. -/
  C : Type v
  /-- The system. -/
  rel : System Ax C

/-- Systems and sound translations form a category. -/
instance Sys.category : Category.{max u v} Sys.{u, v} where
  Hom S T := Translation S.rel T.rel
  id S := Translation.id S.rel
  comp f g := Translation.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A witness translation: maps of contexts and conclusions together with a map of witnesses. -/
structure WTranslation {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'}
    (W : WSystem.{u, v, w} Ax C) (V : WSystem.{u', v', w'} Ax' C') where
  /-- The map of contexts. -/
  ax : Ax → Ax'
  /-- The map of conclusions. -/
  c : C → C'
  /-- The map of witnesses. -/
  map : ∀ a φ, W a φ → V (ax a) (c φ)

namespace WTranslation

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'} {Ax'' : Type u''}
  {C'' : Type v''}

/-- The identity witness translation. -/
def id (W : WSystem.{u, v, w} Ax C) : WTranslation W W := ⟨fun a => a, fun c => c, fun _ _ x => x⟩

/-- Composition of witness translations (first `f`, then `g`). -/
def comp {W : WSystem.{u, v, w} Ax C} {V : WSystem.{u', v', w'} Ax' C'}
    {U : WSystem.{u'', v'', w''} Ax'' C''} (f : WTranslation W V) (g : WTranslation V U) :
    WTranslation W U :=
  ⟨g.ax ∘ f.ax, g.c ∘ f.c, fun a φ x => g.map _ _ (f.map a φ x)⟩

/-- Erasing witnesses turns a witness translation into a sound translation. -/
def erase {W : WSystem.{u, v, w} Ax C} {V : WSystem.{u', v', w'} Ax' C'}
    (f : WTranslation W V) : Translation W.erase V.erase :=
  ⟨f.ax, f.c, fun a φ ⟨x⟩ => ⟨f.map a φ x⟩⟩

end WTranslation

/-- A witness system bundled with its context and conclusion types. -/
structure WSys : Type (max (u + 1) (v + 1) (w + 1)) where
  /-- The contexts. -/
  Ax : Type u
  /-- The conclusions. -/
  C : Type v
  /-- The witness system. -/
  rel : WSystem.{u, v, w} Ax C

/-- Witness systems and witness translations form a category. -/
instance WSys.category : Category.{max u v w} WSys.{u, v, w} where
  Hom W V := WTranslation W.rel V.rel
  id W := WTranslation.id W.rel
  comp f g := WTranslation.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Erasure of witnesses is a functor from witness systems to systems. -/
def WSys.erase : WSys.{u, v, w} ⥤ Sys.{u, v} where
  obj W := ⟨W.Ax, W.C, W.rel.erase⟩
  map f := WTranslation.erase f
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Consequence
