module

public import Silmaril.Wasm.Institution.GameInst.Defs
public import Silmaril.Games.Reduct.Thms

/-!
# Interfaces with bijective imports, and their games

The base definitions of `Silmaril.Wasm.Institution.SpecGInst.Defs`:

* `IfaceB Ty`: typed interfaces (`Silmaril.Wasm.Spec.Iface`) whose morphisms `BHom Z X` are interface
  morphisms `Z ⟶ X` whose import map is a bijection, given with its inverse. They are the
  morphisms along which a `Spec` observation does not erase imports;
* `sigOfHom h`: the renaming of `sigOf A R n` into `sigOf A R m` along `h : Fin n → Fin m`;
* `specHom f : specGame A R Z ⟶ specGame A R X`: imports renamed back along the inverse,
  exports forward along `f.exp`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.SpecGInst

open CategoryTheory Silmaril.Games Silmaril.Wasm.Spec Silmaril.Wasm.Institution.GameInst

variable {Ty : Type}

/-- An interface morphism whose import map is a bijection, with its inverse. -/
structure BHom (Z X : Iface Ty) where
  /-- The interface morphism. -/
  hom : Z ⟶ X
  /-- The inverse of the import map. -/
  inv : X.Imp → Z.Imp
  inv_imp : ∀ i, inv (hom.imp i) = i
  imp_inv : ∀ i, hom.imp (inv i) = i

/-- The identity. -/
def BHom.id (X : Iface Ty) : BHom X X := ⟨𝟙 X, fun i => i, fun _ => rfl, fun _ => rfl⟩

/-- Composition. -/
def BHom.comp {X Y Z : Iface Ty} (f : BHom X Y) (g : BHom Y Z) : BHom X Z where
  hom := f.hom ≫ g.hom
  inv i := f.inv (g.inv i)
  inv_imp i := by
    change f.inv (g.inv (g.hom.imp (f.hom.imp i))) = i
    rw [g.inv_imp, f.inv_imp]
  imp_inv i := by
    change g.hom.imp (f.hom.imp (f.inv (g.inv i))) = i
    rw [f.imp_inv, g.imp_inv]

/-- Typed interfaces, with import-bijective morphisms. -/
structure IfaceB (Ty : Type) where
  /-- The interface. -/
  X : Iface Ty

/-- Interfaces and import-bijective morphisms form a category. -/
instance IfaceB.category : Category.{0} (IfaceB Ty) where
  Hom Z X := BHom Z.X X.X
  id X := BHom.id X.X
  comp f g := BHom.comp f g
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc _ _ _ := rfl

/-- The inclusion of import-bijective morphisms into all interface morphisms. -/
def IfaceB.incl : IfaceB Ty ⥤ Iface Ty where
  obj X := X.X
  map f := BHom.hom f
  map_id _ := rfl
  map_comp _ _ := rfl

variable {A R : Type}

/-- The renaming of `sigOf A R n` into `sigOf A R m` along `h`. -/
def sigOfHom {n m : ℕ} (h : Fin n → Fin m) : Silmaril.Games.Sig.Hom (sigOf A R n) (sigOf A R m) :=
  ⟨fun ia => (h ia.1, ia.2), fun _ r => r⟩

/-- The game morphism of an import-bijective interface morphism. -/
def specHom {Z X : IfaceB Ty} (f : Z ⟶ X) : specGame A R Z.X ⟶ specGame A R X.X :=
  (⟨sigOfHom (A := A) (R := R) (BHom.inv f), sigOfHom (A := A) (R := R) (BHom.hom f).exp⟩ :
    Game.Hom (specGame A R Z.X) (specGame A R X.X))

/-- **The games of interfaces**, as a functor. -/
def specΦ (A R : Type) : IfaceB Ty ⥤ Game.{0} where
  obj X := specGame A R X.X
  map f := specHom f
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Wasm.Institution.SpecGInst
