module

public import Silmaril.Numeric.Libm.Glibc.Defs
public import Silmaril.Numeric.Libm.Lattice.Thms

/-! # The most-platform bounds imply the all-platform bounds -/

@[expose] public section

namespace Silmaril.Numeric.Libm.Glibc

theorem double240_most_le_all : ∀ d ∈ double240, d.most ≤ d.all := by decide

theorem bound_most_le_all (name : String) :
    bound Documented.most name ≤ bound Documented.all name := by
  unfold bound
  cases h : double240.find? (·.name == name) with
  | none => simp
  | some d => exact double240_most_le_all d (List.mem_of_find?_eq_some h)

theorem mostPlatforms_implies_allPlatforms (name : String) :
    (mostPlatforms name).Implies (allPlatforms name) :=
  bound_most_le_all name

example : mostPlatforms "sin" = .glibc 1 := by decide
example : allPlatforms "tan" = .glibc 1 := by decide
example : mostPlatforms "tan" = .glibc 0 := by decide

end Silmaril.Numeric.Libm.Glibc
