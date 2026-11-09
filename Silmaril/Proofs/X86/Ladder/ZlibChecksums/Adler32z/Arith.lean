module

public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Thms
public import Silmaril.X86.Stencils.AccumFold.Thms
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# `adler32_z`: the arithmetic

* `magic_div`: gcc's `x / 65521` by multiply-high (`m = 2^64 + 0xf00e10d2fc5cd = ⌈2^80/65521⌉`,
  then `((x - q) >> 1 + q) >> 15`) is exact on all 64-bit `x`;
* `modW`: the same at `BitVec 64`, in the shape the machine computes it (`mul`, `sub`,
  `shr`, `add`, `shr`, `imul $0xfff1`, `sub`): the result is `x % 65521`;
* `S k`, `R k j`: the reduced sums after `k` bytes (zlib reduces at chunk ends) and the raw
  sums `j` bytes into the chunk that starts at `k`; `red_R` (reducing the raw sums gives the
  reduced sums further on), `R_lt` (below `2^32` within an `NMAX` chunk), `R_succ`,
  `R_add16` (one `DO16` block).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Stencils.AccumFold
open Silmaril.X86.Ladder.ZlibChecksums

/-! ## Division by `BASE` -/

/-- gcc's magic constant (the low 64 bits of `⌈2^80 / 65521⌉`). -/
def MAGIC : Nat := 0xf00e10d2fc5cd

theorem magic_div (x : Nat) (hx : x < 2 ^ 64) :
    ((x - x * MAGIC / 2 ^ 64) / 2 + x * MAGIC / 2 ^ 64) / 2 ^ 15 = x / 65521 := by
  set q := x * MAGIC / 2 ^ 64 with hq
  have hqx : q ≤ x := by
    rw [hq]; apply Nat.div_le_of_le_mul; unfold MAGIC; nlinarith
  have h1 : (x - q) / 2 + q = (x + q) / 2 := by omega
  rw [h1, Nat.div_div_eq_div_mul]
  have h2 : x + q = (x * (2 ^ 64 + MAGIC)) / 2 ^ 64 := by
    rw [hq, Nat.mul_add, Nat.mul_comm x (2 ^ 64), Nat.mul_add_div (by norm_num)]
  rw [h2, Nat.div_div_eq_div_mul]
  have hd := Nat.div_add_mod x 65521
  have hr := Nat.mod_lt x (show 0 < 65521 by norm_num)
  have hq0 : x / 65521 < 2 ^ 49 := by omega
  set q0 := x / 65521
  set r := x % 65521
  apply Nat.div_eq_of_lt_le
  · rw [← hd]; unfold MAGIC; nlinarith
  · rw [← hd]; unfold MAGIC; nlinarith

theorem modW (x q : Word) (hq : q = BitVec.ofNat 64 (x.toNat * MAGIC / 2 ^ 64)) :
    x - ((q + (x - q) >>> 1) >>> 15) * 65521#64 = BitVec.ofNat 64 (x.toNat % 65521) := by
  have hx := x.isLt
  have hm := magic_div x.toNat hx
  have hqv : q.toNat = x.toNat * MAGIC / 2 ^ 64 := by
    rw [hq, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul; unfold MAGIC; nlinarith
  have hqx : q.toNat ≤ x.toNat := by
    rw [hqv]; apply Nat.div_le_of_le_mul; unfold MAGIC; nlinarith
  set Q := x.toNat * MAGIC / 2 ^ 64
  have hd : x.toNat / 65521 * 65521 ≤ x.toNat := Nat.div_mul_le_self _ _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e1 : (2 ^ 64 - q.toNat + x.toNat) % 2 ^ 64 = x.toNat - q.toNat := by omega
  rw [e1]
  have e2 : (q.toNat + (x.toNat - q.toNat) / 2 ^ 1) % 2 ^ 64 = (x.toNat - q.toNat) / 2 + q.toNat := by
    omega
  rw [e2, hqv, hm]
  have e3 : x.toNat / 65521 * (65521 % 2 ^ 64) % 2 ^ 64 = x.toNat / 65521 * 65521 := by
    norm_num; omega
  rw [e3]
  have := Nat.div_add_mod x.toNat 65521
  have h5 := Nat.mod_lt x.toNat (show 0 < 65521 by norm_num)
  omega

theorem modW' (x q : Word) (hq : q = BitVec.ofNat 64 (x.toNat * MAGIC / 2 ^ 64)) :
    x - (((x - q) >>> 1 + q) >>> 15) * 65521#64 = BitVec.ofNat 64 (x.toNat % 65521) := by
  rw [BitVec.add_comm]; exact modW x q hq

/-- `modW'` on a word given by its value, in the form `simp` leaves it. -/
theorem modWN (y : Nat) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 y - (((BitVec.ofNat 64 y - BitVec.ofNat 64 (y % 18446744073709551616 *
      4223091239536077 / 18446744073709551616)) >>> 1 + BitVec.ofNat 64 (y % 18446744073709551616 *
      4223091239536077 / 18446744073709551616)) >>> 15) * 65521#64 = BitVec.ofNat 64 (y % 65521) := by
  have := modW' (BitVec.ofNat 64 y) _ rfl
  simp only [BitVec.toNat_ofNat, MAGIC, Nat.reducePow] at this
  rw [this, Nat.mod_eq_of_lt (show y < 18446744073709551616 from hy)]

/-- `modW'` on any word, in the form `simp` leaves it. -/
theorem modWX (x : Word) :
    x - (((x - BitVec.ofNat 64 (x.toNat * 4223091239536077 / 18446744073709551616)) >>> 1 +
      BitVec.ofNat 64 (x.toNat * 4223091239536077 / 18446744073709551616)) >>> 15) * 65521#64 =
      BitVec.ofNat 64 (x.toNat % 65521) :=
  modW' x _ rfl

/-! ## The sums -/

/-- The reduced sums after the first `k` bytes. -/
def S (bs : List Byte) (a k : Nat) : Nat × Nat := modFold BASE (adlerStart a) (bs.take k)

/-- The raw sums `j` bytes into the chunk that starts after byte `k`. -/
def R (bs : List Byte) (a k j : Nat) : Nat × Nat := rawFold (S bs a k) ((bs.drop k).take j)

theorem modFold_lt : ∀ (s : Nat × Nat) (xs : List Byte), s.1 < BASE → s.2 < BASE →
    (modFold BASE s xs).1 < BASE ∧ (modFold BASE s xs).2 < BASE
  | s, [], h1, h2 => ⟨h1, h2⟩
  | s, x :: xs, _, _ => by
    simp only [modFold, List.foldl_cons]
    exact modFold_lt _ xs (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

theorem start_lt (a : Nat) : (adlerStart a).1 < BASE ∧ (adlerStart a).2 < BASE :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem S_lt (bs : List Byte) (a k : Nat) : (S bs a k).1 < BASE ∧ (S bs a k).2 < BASE :=
  modFold_lt _ _ (start_lt a).1 (start_lt a).2

theorem red_S (bs : List Byte) (a k : Nat) : red BASE (S bs a k) = S bs a k := by
  have := S_lt bs a k
  simp only [red, Nat.mod_eq_of_lt this.1, Nat.mod_eq_of_lt this.2]

theorem red_R (bs : List Byte) (a k j : Nat) : red BASE (R bs a k j) = S bs a (k + j) := by
  rw [R, rawFold_mod, red_S, S, S, List.take_add, modFold_append]

theorem R_zero (bs : List Byte) (a k : Nat) : R bs a k 0 = S bs a k := by simp [R, rawFold]

theorem R_lt (bs : List Byte) (a k j : Nat) (hj : j ≤ NMAX) :
    (R bs a k j).1 < 2 ^ 32 ∧ (R bs a k j).2 < 2 ^ 32 :=
  rawFold_lt nmax_bound (S_lt bs a k).1 (S_lt bs a k).2
    (by simp only [List.length_take]; omega)

theorem R_succ (bs : List Byte) (a k j : Nat) (h : k + j < bs.length) :
    R bs a k (j + 1) = rawStep (R bs a k j) (bs.getD (k + j) 0) := by
  simp only [R]
  rw [List.take_add_one, rawFold_append]
  have : ((bs.drop k)[j]?) = some (bs.getD (k + j) 0) := by
    rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k + j < bs.length by omega)]
  rw [this]; rfl

theorem rawFold_fst_le : ∀ (s : Nat × Nat) (xs : List Byte), (rawFold s xs).1 ≤ s.1 + 255 * xs.length
  | s, [] => by simp [rawFold]
  | s, x :: xs => by
    have := rawFold_fst_le (rawStep s x) xs
    have hx := x.isLt
    simp only [rawFold, List.foldl_cons, List.length_cons, rawStep] at this ⊢
    change (rawFold _ xs).1 ≤ _ at this
    change (rawFold _ xs).1 ≤ _
    omega

theorem R1_le (bs : List Byte) (a k j : Nat) : (R bs a k j).1 ≤ (S bs a k).1 + 255 * j := by
  have := rawFold_fst_le (S bs a k) ((bs.drop k).take j)
  simp only [List.length_take, List.length_drop] at this
  simp only [R]
  have : min j (bs.length - k) ≤ j := Nat.min_le_left _ _
  have : 255 * min j (bs.length - k) ≤ 255 * j := Nat.mul_le_mul_left _ this
  omega

theorem S_full (bs : List Byte) (a : Nat) : S bs a bs.length = modFold BASE (adlerStart a) bs := by
  simp [S]

/-! ## Machine words -/

theorem ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
