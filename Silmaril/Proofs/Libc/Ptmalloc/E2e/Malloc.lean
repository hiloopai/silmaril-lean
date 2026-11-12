module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.MallocKit
public import Silmaril.Libc.Ptmalloc.Config.Defs

/-!
# ptmalloc end to end: the code's tcache index is the model's, for any LP64 configuration

`hitBin_utidx`: the bin gcc's `__libc_malloc` computes (`X86sim.Malloc.hitBin`, the shared
`lea 0x17`, `and $~0xf`, `lea -0x11`, `shr $4` with the `MINSIZE` branch of glibc 2.36, 2.39 and
2.40) is `C.utidx n` for every configuration with `SIZE_SZ = 8`, 16-byte alignment and
`MINSIZE = 32`. The proof is `E2e.hitBin_eq`'s (`Silmaril.Proofs.Libc.Ptmalloc.E2e.V239`), stated
for any such `C` and for the code-independent `hitBin`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Libc.Ptmalloc.E2e

/-- `x &&& (2^64 - 16)` clears the low four bits. -/
theorem and_mask16 (x : Nat) (hx : x < 2 ^ 64) : x &&& (2 ^ 64 - 16) = x / 16 * 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h16 : (2 ^ 64 - 16 : Nat) = (2 ^ 60 - 1) * 2 ^ 4 := by decide
  have h16' : x / 16 * 16 = x / 2 ^ 4 * 2 ^ 4 := rfl
  rw [h16, h16', Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hi : 4 ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.sub_add_cancel hi]
    by_cases h64 : i < 64
    · simp [show i - 4 < 60 by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  · simp [hi]

/-- **The code's tcache bin is the model's**, for any LP64 configuration. -/
theorem hitBin_utidx {C : Config} (h8 : C.sizeSz = 8) (h16 : C.align = 16) (h32 : C.minSize = 32)
    (h15 : C.alignMask = 15) {n : Nat} (hn : n < 2 ^ 63) :
    X86sim.Malloc.hitBin n = C.utidx n := by
  have hadd : (BitVec.ofNat 64 n + 0x17#64).toNat = n + 23 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (0x17#64).toNat = 23 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold X86sim.Malloc.hitBin X86sim.Malloc.tcIdx Config.utidx Config.tidx Config.request2size
  rw [h8, h16, h32, h15, hadd]
  by_cases hs : n + 23 ≤ 0x1f
  · simp only [hs, ite_true, show n + 8 + 15 < 32 by omega]
    rfl
  · simp only [hs, ite_false, show ¬ n + 8 + 15 < 32 by omega]
    have hand : ((BitVec.ofNat 64 n + 0x17#64) &&& 0xfffffffffffffff0#64).toNat = (n + 23) / 16 * 16 := by
      rw [BitVec.toNat_and, hadd, show (0xfffffffffffffff0#64).toNat = 2 ^ 64 - 16 by rfl]
      exact and_mask16 _ (by omega)
    have hsub : (((BitVec.ofNat 64 n + 0x17#64) &&& 0xfffffffffffffff0#64) - 0x11#64).toNat =
        (n + 23) / 16 * 16 - 17 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hand]; simp; omega), hand]
      rfl
    rw [BitVec.toNat_ushiftRight, hsub, Nat.shiftRight_eq_div_pow]
    omega

end Silmaril.Libc.Ptmalloc.E2e
