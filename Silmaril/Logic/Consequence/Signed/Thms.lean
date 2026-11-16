module

public import Silmaril.Logic.Consequence.Signed.Defs
public import Mathlib.Algebra.Group.Basic

/-!
# Signed formulas: laws

`Signed.neg_pos`, `Signed.neg_neg_atom`: negation flips the sign. `isPos_neg`, `atom_neg`: it flips
the polarity and keeps the atom. `eq_of_isPos_atom`: a signed formula is determined by its
polarity and atom, so `Signed` decomposes, unlike an arbitrary involutive negation.
`neg_ne_self`: `Signed` has no fixed point of negation. `negateEach_negateEach`, `negateEach_append`,
`mem_negateEach`, `length_negateEach`.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u

namespace Signed

variable {A : Type u}

@[simp] theorem neg_pos (a : A) : -(pos a) = neg a := rfl
@[simp] theorem neg_neg_atom (a : A) : -(neg a) = pos a := rfl

@[simp] theorem isPos_neg (x : Signed A) : (-x).isPos = !x.isPos := by cases x <;> rfl
@[simp] theorem atom_neg (x : Signed A) : (-x).atom = x.atom := by cases x <;> rfl

theorem eq_of_isPos_atom {x y : Signed A} (h₁ : x.isPos = y.isPos) (h₂ : x.atom = y.atom) :
    x = y := by
  cases x <;> cases y <;> simp_all [isPos, atom]

theorem neg_ne_self (x : Signed A) : -x ≠ x := by cases x <;> simp

theorem pos_injective : Function.Injective (pos : A → Signed A) := fun _ _ h => by cases h; rfl

end Signed

variable {α : Type u}

@[simp] theorem negateEach_nil [Neg α] : negateEach ([] : List α) = [] := rfl

@[simp] theorem negateEach_cons [Neg α] (a : α) (l : List α) :
    negateEach (a :: l) = -a :: negateEach l := rfl

theorem negateEach_append [Neg α] (l l' : List α) :
    negateEach (l ++ l') = negateEach l ++ negateEach l' := List.map_append

@[simp] theorem length_negateEach [Neg α] (l : List α) : (negateEach l).length = l.length :=
  List.length_map _

@[simp] theorem negateEach_negateEach [InvolutiveNeg α] (l : List α) :
    negateEach (negateEach l) = l := by simp [negateEach]

theorem mem_negateEach [InvolutiveNeg α] {a : α} {l : List α} : a ∈ negateEach l ↔ -a ∈ l := by
  simp [negateEach, neg_eq_iff_eq_neg]

end Silmaril.Consequence
