module

public import Silmaril.Raw.X86.Str9G.Simd

/-! # 128-bit values and their bytes

`xmm_ext` (two values with the same 16 bytes are equal), `byteOf_load` (byte `i` of a
little-endian load of `bs` is `bs[i]`), `byteOf_zero`. -/

@[expose] public section

namespace Silmaril.Raw.X86.Str9G

open Silmaril.X86.Str9G
open Silmaril.X86.Sse9 (Xmm)

theorem digits_low {k : Nat} (N : Nat) :
    ∀ n, digits k (fun i => N / 2 ^ (k * i) % 2 ^ k) n = N % 2 ^ (k * n)
  | 0 => by simp [digits, Nat.mod_one]
  | n + 1 => by
    simp only [digits, digits_low N n]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul, Nat.mul_comm (2 ^ (k * n))]

theorem digits_succ_low {k : Nat} (a : Nat → Nat) :
    ∀ n, digits k a (n + 1) = a 0 + 2 ^ k * digits k (fun i => a (i + 1)) n
  | 0 => by simp [digits]
  | n + 1 => by
    rw [digits, digits_succ_low a n, digits]
    rw [show k * (n + 1) = k + k * n by rw [Nat.mul_succ, Nat.add_comm], Nat.pow_add, Nat.mul_add,
      Nat.add_assoc, Nat.mul_left_comm]

theorem byteOf_toNat (x : Xmm) (i : Nat) : (byteOf x i).toNat = x.toNat / 2 ^ (8 * i) % 2 ^ 8 := by
  unfold byteOf; simp [Nat.shiftRight_eq_div_pow]

/-- **Two 128-bit values with the same sixteen bytes are equal.** -/
theorem xmm_ext {x y : Xmm} (h : ∀ i < 16, byteOf x i = byteOf y i) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat = digits 8 (fun i => x.toNat / 2 ^ (8 * i) % 2 ^ 8) 16 := by
    rw [digits_low]; exact (Nat.mod_eq_of_lt x.isLt).symm
  have hy : y.toNat = digits 8 (fun i => y.toNat / 2 ^ (8 * i) % 2 ^ 8) 16 := by
    rw [digits_low]; exact (Nat.mod_eq_of_lt y.isLt).symm
  rw [hx, hy]
  have : ∀ n, n ≤ 16 → digits 8 (fun i => x.toNat / 2 ^ (8 * i) % 2 ^ 8) n =
      digits 8 (fun i => y.toNat / 2 ^ (8 * i) % 2 ^ 8) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [digits]
      rw [ih (by omega), ← byteOf_toNat, ← byteOf_toNat, h n (by omega)]
  exact this 16 le_rfl

theorem leValue_digits (bs : List (BitVec 8)) :
    Silmaril.X86.Ext.leValue bs = digits 8 (fun i => (bs.getD i 0).toNat) bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, digits_succ_low, Silmaril.X86.Ext.leValue, ih]
    simp

/-- **Byte `i` of a little-endian load of sixteen bytes is the `i`-th byte.** -/
theorem byteOf_load {bs : List (BitVec 8)} (hl : bs.length = 16) {i : Nat} (hi : i < 16) :
    byteOf (BitVec.ofNat 128 (Silmaril.X86.Ext.leValue bs)) i = bs.getD i 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [byteOf_toNat, BitVec.toNat_ofNat, leValue_digits, hl]
  have hlt : digits 8 (fun i => (bs.getD i 0).toNat) 16 < 2 ^ 128 :=
    digits_lt (k := 8) (fun j => (bs.getD j 0).isLt) 16
  rw [Nat.mod_eq_of_lt hlt, ← Nat.shiftRight_eq_div_pow]
  exact digits_get (k := 8) (fun j => (bs.getD j 0).isLt) 16 i hi

theorem byteOf_zero (i : Nat) : byteOf 0 i = 0 := by unfold byteOf; simp

end Silmaril.Raw.X86.Str9G
