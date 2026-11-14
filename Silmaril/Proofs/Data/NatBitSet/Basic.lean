module

public import Silmaril.Data.NatBitSet.Defs
import Init.Data.Nat.Bitwise.Lemmas

/-!
# Bit-mask sets: completeness
-/

@[expose] public section

namespace Silmaril.Proofs.Data.NatBitSet

open Silmaril.Data Silmaril.Data.NatBitSet

theorem mem_insert' (s : NatBitSet) (k j : Nat) :
    (s.insert k).mem j = (s.mem j || decide (k = j)) := by
  simp [NatBitSet.mem, NatBitSet.insert, Nat.testBit_or, Nat.testBit_two_pow]

/-- **Completeness**: every finitely supported predicate is a set. -/
theorem exists_of_finite (f : Nat → Bool) (n : Nat) (hf : ∀ k, n ≤ k → f k = false) :
    ∃ s : NatBitSet, ∀ k, s.mem k = f k := by
  induction n generalizing f with
  | zero => exact ⟨empty, fun k => by rw [show empty.mem k = false from Nat.zero_testBit k, hf k (Nat.zero_le _)]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih (fun k => f k && decide (k ≠ n)) fun k hk => by
      by_cases h : k = n
      · simp [h]
      · simp [hf k (by omega)]
    refine ⟨if f n then s.insert n else s, fun k => ?_⟩
    have := hs k
    by_cases hk : k = n
    · subst hk; cases h : f k <;> simp_all [mem_insert']
    · cases h : f n <;> simp_all [mem_insert', Ne.symm hk]

end Silmaril.Proofs.Data.NatBitSet
