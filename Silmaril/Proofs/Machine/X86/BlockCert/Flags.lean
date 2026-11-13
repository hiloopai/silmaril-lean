module

public import Silmaril.X86.Ext.Flags

/-!
# Flag lemmas for block VCs

The carry of an `n`-bit addition is the unsigned wrap test `x + y <ᵤ x`; the signed
conditions after `cmp x, y` are `x <ₛ y` and `x ≤ₛ y`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.BlockCert

open Silmaril.X86.Ext

variable {w : Nat}

theorem addCarryN_eq (x y : BitVec (w + 1)) : addCarryN x y = BitVec.carry (w + 1) x y false := by
  rw [BitVec.carry_succ]
  simp only [addCarryN, BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not]
  simp only [BitVec.getLsbD_add (Nat.lt_succ_self w), Nat.lt_succ_self, decide_true,
    Bool.true_and]
  cases x.getLsbD w <;> cases y.getLsbD w <;> cases BitVec.carry w x y false <;> rfl

theorem addCarryN_eq_ult (x y : BitVec (w + 1)) : addCarryN x y = (x + y).ult x := by
  rw [addCarryN_eq]
  simp only [BitVec.carry, BitVec.ult, BitVec.toNat_add, Bool.toNat_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
  have := x.isLt; have := y.isLt
  apply decide_eq_decide.mpr
  by_cases h : 2 ^ (w + 1) ≤ x.toNat + y.toNat
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem eval_l_sub (x y : BitVec (w + 1)) : Cond.eval (subFlagsN x y) .l = some (x.slt y) := by
  simp only [Cond.eval, subFlagsN, kXor, slt_eq_sign_xor_overflow]

theorem eval_le_sub (x y : BitVec (w + 1)) :
    Cond.eval (subFlagsN x y) .le = some (x.sle y) := by
  simp only [Cond.eval, subFlagsN, kXor, isZeroN_sub]
  rw [BitVec.sle_eq_slt_or_eq, slt_eq_sign_xor_overflow]
  cases h : x == y <;> cases (x - y).msb ^^ subOverflowN x y <;> simp_all [kOr]

end Silmaril.Proofs.Machine.X86.BlockCert
