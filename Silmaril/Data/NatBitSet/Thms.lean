module

public import Silmaril.Data.NatBitSet.Defs
import Init.Data.Nat.Bitwise.Lemmas
import Silmaril.Proofs.Data.NatBitSet.Basic

/-!
# Bit-mask sets: membership specifications and extensionality

`ext_iff` and `exists_of_finite` make `mem` a bijection from `NatBitSet` onto the
finitely supported predicates `Nat → Bool`.
-/

@[expose] public section

namespace Silmaril.Data.NatBitSet

theorem mem_empty (k : Nat) : empty.mem k = false := Nat.zero_testBit k

theorem mem_insert (s : NatBitSet) (k j : Nat) : (s.insert k).mem j = (s.mem j || decide (k = j)) := by
  simp [mem, insert, Nat.testBit_or, Nat.testBit_two_pow]

theorem mem_erase (s : NatBitSet) (k j : Nat) : (s.erase k).mem j = (s.mem j && !decide (k = j)) := by
  simp only [mem, erase, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow]
  cases s.bits.testBit j <;> cases decide (k = j) <;> rfl

theorem mem_union (s t : NatBitSet) (k : Nat) : (s.union t).mem k = (s.mem k || t.mem k) :=
  Nat.testBit_or _ _ _

theorem mem_inter (s t : NatBitSet) (k : Nat) : (s.inter t).mem k = (s.mem k && t.mem k) :=
  Nat.testBit_and _ _ _

theorem mem_diff (s t : NatBitSet) (k : Nat) : (s.diff t).mem k = (s.mem k && !t.mem k) := by
  simp only [mem, diff, Nat.testBit_and, Nat.testBit_xor]
  cases s.bits.testBit k <;> cases t.bits.testBit k <;> rfl

/-- **Extensionality**: the representation is canonical. -/
theorem ext_iff {s t : NatBitSet} : s = t ↔ ∀ k, s.mem k = t.mem k :=
  ⟨fun h _ => h ▸ rfl, fun h => congrArg mk (Nat.eq_of_testBit_eq h)⟩

/-- Members lie below the bit length of the mask. -/
theorem mem_eq_false_of_le {s : NatBitSet} {k : Nat} (h : s.bits < 2 ^ k) : s.mem k = false :=
  Nat.testBit_lt_two_pow h

/-- **Completeness**: every finitely supported predicate is a set. -/
theorem exists_of_finite (f : Nat → Bool) (n : Nat) (hf : ∀ k, n ≤ k → f k = false) :
    ∃ s : NatBitSet, ∀ k, s.mem k = f k :=
  Proofs.Data.NatBitSet.exists_of_finite f n hf

end Silmaril.Data.NatBitSet
