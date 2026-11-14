module

public import Silmaril.Net.Hpack.Integer.Thms

/-!
# QPACK prefix integers: helper lemmas

QPACK reuses HPACK's prefix integers unmodified (RFC 9204 §4.1.1). These lemmas describe the
first octet of `encodeInt`, which QPACK's decoders dispatch on; they restate, for the QPACK
proofs, facts proved privately in HPACK's proof module.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Qpack

open Silmaril.Net.Hpack

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

/-- Flag bits `hi` (a multiple of `2^n` below 256) leave room for an `n`-bit prefix. -/
theorem flags_room {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256) :
    hi + 2 ^ n ≤ 256 := by
  obtain ⟨k, rfl⟩ : 2 ^ n ∣ hi := Nat.dvd_of_mod_eq_zero hhi
  obtain ⟨j, hj⟩ : 2 ^ n ∣ 256 := by
    have : (256 : Nat) = 2 ^ 8 := by decide
    rw [this]; exact Nat.pow_dvd_pow 2 hn8
  have : k < j := by
    rw [hj] at hhi'
    exact Nat.lt_of_mul_lt_mul_left hhi'
  calc 2 ^ n * k + 2 ^ n = 2 ^ n * (k + 1) := (Nat.mul_succ _ _).symm
    _ ≤ 2 ^ n * j := Nat.mul_le_mul_left _ this
    _ = 256 := hj.symm

/-- The first octet of an encoded integer carries the flag bits `hi` and the prefix. -/
theorem encodeInt_head {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) : ∃ tl, encodeInt n hi i = (hi + min i (prefixMax n)).toUInt8 :: tl ∧
      (hi + min i (prefixMax n)) < 256 ∧ min i (prefixMax n) < 2 ^ n := by
  have hp := Nat.two_pow_pos n
  have hk := flags_room hn8 hhi hhi'
  have hm : prefixMax n = 2 ^ n - 1 := rfl
  unfold encodeInt
  by_cases h : i < prefixMax n
  · exact ⟨[], by simp [h, Nat.min_eq_left (Nat.le_of_lt h)], by omega, by omega⟩
  · exact ⟨encodeRest (i - prefixMax n), by simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)],
      by omega, by omega⟩

/-- An encoded integer followed by `rest`: its first octet lies in `[hi, hi + 2^n)` and the
decoder reads the integer back, stopping at `rest`. -/
theorem encodeInt_split {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) (rest : List UInt8) : ∃ b tl, encodeInt n hi i ++ rest = b :: tl ∧
      hi ≤ b.toNat ∧ b.toNat < hi + 2 ^ n ∧ decodeInt n (b :: tl) = some (i, rest) := by
  obtain ⟨tl, he, hlt, hv⟩ := encodeInt_head hn8 hhi hhi' i
  have hd := decodeInt_encodeInt hn8 hhi hhi' i rest
  rw [he] at hd
  refine ⟨_, tl ++ rest, by rw [he]; rfl, ?_, ?_, hd⟩ <;>
    simp only [toNat_toUInt8, Nat.mod_eq_of_lt hlt] <;> omega

theorem encodeInt_ne_nil (n hi i : Nat) : encodeInt n hi i ≠ [] := by
  unfold encodeInt; split <;> simp

end Silmaril.Proofs.Net.Qpack
