module

public import Silmaril.X86.Ext9.Defs

/-!
# `Ext9` semantic facts

`bsrIndex_eq_log2`: on a nonzero source the BSR index is `⌊log2⌋` of the source.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ext9

open Silmaril.X86.Ext9

theorem bsrIndex_eq_log2 {n : Nat} (x : BitVec n) (hx : x ≠ 0#n) :
    bsrIndex x = Nat.log2 x.toNat := by
  have hpos : x.toNat ≠ 0 := by
    intro h; apply hx; exact BitVec.eq_of_toNat_eq (by simp [h])
  have hkn : Nat.log2 x.toNat < n := (Nat.log2_lt hpos).mpr x.isLt
  have hbit : x.getLsbD (Nat.log2 x.toNat) = true := by
    rw [BitVec.getLsbD, Nat.testBit_log2 hpos]
  have habove : ∀ j, Nat.log2 x.toNat < j → x.getLsbD j = false := by
    intro j hj
    rw [BitVec.getLsbD]
    apply Nat.testBit_lt_two_pow
    exact lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hj)
  unfold bsrIndex Silmaril.X86.Ext.lzcntN
  have hf : (List.range n).find? (fun i => x.getLsbD (n - 1 - i)) =
      some (n - 1 - Nat.log2 x.toNat) := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by rw [show n - 1 - (n - 1 - Nat.log2 x.toNat) = Nat.log2 x.toNat by omega]; exact hbit,
      n - 1 - Nat.log2 x.toNat, by simp; omega, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range]
    rw [habove _ (by omega)]; rfl
  rw [hf]; simp only [Option.getD_some]; omega

end Silmaril.Proofs.X86.Ext9
