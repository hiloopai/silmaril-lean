module

public import Silmaril.Logic.Consequence.Translation.Defs
public import Silmaril.Logic.Consequence.Thms
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Translations between consequence systems: laws

**Category laws.** `id_comp`, `comp_id`, `comp_assoc` for `Translation`; `Sys.category` and
`WSys.category` are Mathlib categories (`Defs`), and `Sys.hom_ext`: morphisms are determined by
their two maps.

**Pullback as the cartesian lift.** `nonempty_translation_iff`: a translation with maps `(f, g)`
exists iff `S ≤ T.pullback f g`, and it is then unique (`translation_subsingleton`).
`Translation.toPullback`: the canonical translation `T.pullback f g ⟶ T`, which is
conservative (`toPullback_conservative`); every translation factors through it
(`factor_toPullback`).

**Forgetful functor.** `Sys.forget : Sys ⥤ Type u × Type v`
sends a system to its two types and a translation to its two maps; it is faithful on
morphisms (`Sys.forget_map_injective`).

**Conservativity.** `Conservative.id`, `Conservative.comp`; `ofLE_conservative_iff`: an inclusion
is conservative iff the systems are equal.

**Erasure.** `WSys.erase` is a functor (`Defs`); `WTranslation.erase_ax`, `erase_c`.
-/

@[expose] public section

namespace Silmaril.Consequence

open CategoryTheory

universe u v w u' v' w' u'' v'' u₃ v₃

namespace Translation

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'} {Ax'' : Type u''}
  {C'' : Type v''} {Ax₃ : Type u₃} {C₃ : Type v₃}
  {S : System Ax C} {T : System Ax' C'} {U : System Ax'' C''} {V : System Ax₃ C₃}

@[simp] theorem id_comp (f : Translation S T) : (Translation.id S).comp f = f := rfl
@[simp] theorem comp_id (f : Translation S T) : f.comp (Translation.id T) = f := rfl
theorem comp_assoc (f : Translation S T) (g : Translation T U) (h : Translation U V) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

/-- A translation with given maps exists exactly when `S ≤ T.pullback f g`. -/
theorem nonempty_translation_iff (f : Ax → Ax') (g : C → C') :
    (∃ τ : Translation S T, τ.ax = f ∧ τ.c = g) ↔ S ≤ T.pullback f g :=
  ⟨fun ⟨τ, hf, hg⟩ => hf ▸ hg ▸ τ.sound, fun h => ⟨⟨f, g, h⟩, rfl, rfl⟩⟩

/-- Translations with the same maps are equal: soundness is a proposition. -/
theorem translation_subsingleton {τ σ : Translation S T} (h₁ : τ.ax = σ.ax) (h₂ : τ.c = σ.c) :
    τ = σ := Translation.ext h₁ h₂

/-- The canonical translation from a pullback to the system it reindexes. -/
def toPullback (T : System Ax' C') (f : Ax → Ax') (g : C → C') :
    Translation (T.pullback f g) T := ⟨f, g, le_rfl⟩

theorem toPullback_conservative (T : System Ax' C') (f : Ax → Ax') (g : C → C') :
    (toPullback T f g).Conservative := le_rfl

/-- Every translation factors as an inclusion into the pullback followed by `toPullback`. -/
theorem factor_toPullback (τ : Translation S T) :
    (ofLE τ.sound).comp (toPullback T τ.ax τ.c) = τ := rfl

theorem Conservative.id : (Translation.id S).Conservative := le_rfl

theorem Conservative.comp {f : Translation S T} {g : Translation T U} (hf : f.Conservative)
    (hg : g.Conservative) : (f.comp g).Conservative :=
  fun a φ h => hf a φ (hg (f.ax a) (f.c φ) h)

theorem ofLE_conservative_iff {S T : System Ax C} (h : S ≤ T) :
    (ofLE h).Conservative ↔ S = T :=
  ⟨fun h' => le_antisymm h h', fun e => by subst e; exact le_rfl⟩

end Translation

namespace Sys

theorem hom_ext {S T : Sys.{u, v}} {f g : S ⟶ T} (h₁ : f.ax = g.ax) (h₂ : f.c = g.c) : f = g :=
  Translation.ext h₁ h₂

@[simp] theorem id_ax (S : Sys.{u, v}) : (𝟙 S : S ⟶ S).ax = fun a => a := rfl
@[simp] theorem id_c (S : Sys.{u, v}) : (𝟙 S : S ⟶ S).c = fun c => c := rfl
@[simp] theorem comp_ax {S T U : Sys.{u, v}} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).ax = g.ax ∘ f.ax := rfl
@[simp] theorem comp_c {S T U : Sys.{u, v}} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).c = g.c ∘ f.c := rfl

/-- The underlying pair of types of a system, and the two maps of a translation. -/
def forget : Sys.{u, v} ⥤ Type u × Type v where
  obj S := (S.Ax, S.C)
  map f := (TypeCat.ofHom f.ax, TypeCat.ofHom f.c)

theorem forget_map_injective {S T : Sys.{u, v}} : Function.Injective (forget.map (X := S) (Y := T)) :=
  fun f g h => hom_ext (by simpa [forget] using congrArg (fun p => TypeCat.Hom.hom p.1) h)
    (by simpa [forget] using congrArg (fun p => TypeCat.Hom.hom p.2) h)

end Sys

namespace WTranslation

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'}

@[simp] theorem erase_ax {W : WSystem.{u, v, w} Ax C} {V : WSystem.{u', v', w'} Ax' C'}
    (f : WTranslation W V) : f.erase.ax = f.ax := rfl
@[simp] theorem erase_c {W : WSystem.{u, v, w} Ax C} {V : WSystem.{u', v', w'} Ax' C'}
    (f : WTranslation W V) : f.erase.c = f.c := rfl

end WTranslation

end Silmaril.Consequence
