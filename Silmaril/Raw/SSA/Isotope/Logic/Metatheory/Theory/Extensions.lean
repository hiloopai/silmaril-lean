module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Category
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

@[expose] public section

namespace Silmaril.Logic.Metatheory

open CategoryTheory CategoryTheory.Limits

universe u v

namespace RefinementTheory

variable {S : IndexedSyntax.{u, v}}

/-- Theories containing a specified calculus, ordered by further extension. -/
abbrev Extensions (base : RefinementTheory S) := {R : RefinementTheory S // base ≤ R}

namespace Extensions

variable (base : RefinementTheory S)

/-- Forget the requirement to include the base calculus. -/
def inclusion : Extensions base ⥤ RefinementTheory S where
  obj R := R.val
  map h := homOfLE (leOfHom h)

/-- The base calculus, with no additional equations or refinements. -/
def initial : Extensions base := ⟨base, fun h => h⟩

instance (R : Extensions base) : Unique (initial base ⟶ R) where
  default := homOfLE (fun h => R.property h)
  uniq _ := Subsingleton.elim _ _

def initialIsInitial : IsInitial (initial base) := IsInitial.ofUnique _

instance : HasInitial (Extensions base) := (initialIsInitial base).hasInitial

end Extensions

end RefinementTheory

namespace EquationalTheory

variable {S : IndexedSyntax.{u, v}}

/-- Equational theories containing all equations of a specified calculus. -/
abbrev Extensions (base : EquationalTheory S) := {R : EquationalTheory S // base ≤ R}

namespace Extensions

variable (base : EquationalTheory S)

def inclusion : Extensions base ⥤ EquationalTheory S where
  obj R := R.val
  map h := homOfLE (leOfHom h)

def initial : Extensions base := ⟨base, fun h => h⟩

instance (R : Extensions base) : Unique (initial base ⟶ R) where
  default := homOfLE (fun h => R.property h)
  uniq _ := Subsingleton.elim _ _

def initialIsInitial : IsInitial (initial base) := IsInitial.ofUnique _

instance : HasInitial (Extensions base) := (initialIsInitial base).hasInitial

end Extensions

end EquationalTheory

end Silmaril.Logic.Metatheory
