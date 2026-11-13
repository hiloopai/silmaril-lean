module

public import Silmaril.Net.Hpack.Integer.Defs

/-!
# HPACK integers and string literals: proofs

Round trips of RFC 7541 §5.1 and §5.2, for `Silmaril.Net.Hpack.Integer.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Hpack

open Silmaril.Net.Hpack

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem decodeRest_encodeRest (i : Nat) (rest : List UInt8) :
    decodeRest (encodeRest i ++ rest) = some (i, rest) := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rw [encodeRest]
    by_cases h : i < 128
    · simp only [h, ↓reduceIte, List.singleton_append, decodeRest, toNat_toUInt8,
        Nat.mod_eq_of_lt (show i < 256 by omega)]
    · simp only [h, ↓reduceIte, List.cons_append, decodeRest]
      have hb : ((i % 128 + 128).toUInt8).toNat = i % 128 + 128 := by
        simp only [toNat_toUInt8]; omega
      rw [hb, ih (i / 128) (by omega)]
      simp only [show ¬ (i % 128 + 128 < 128) by omega, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq, and_true]
      omega

theorem encodeRest_ne_nil (i : Nat) : encodeRest i ≠ [] := by
  rw [encodeRest]; split <;> simp

theorem pow_pos_two (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem decodeInt_encodeInt {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0)
    (hhi' : hi < 256) (i : Nat) (rest : List UInt8) :
    decodeInt n (encodeInt n hi i ++ rest) = some (i, rest) := by
  have h2 : 2 ^ n ≤ 256 := by
    calc 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hn8
      _ = 256 := by decide
  have hp := pow_pos_two n
  have hm : prefixMax n = 2 ^ n - 1 := rfl
  -- `hi` is a multiple of `2^n` below 256, so `hi + v < 256` for `v < 2^n`.
  have hk : hi + 2 ^ n ≤ 256 := by
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
  have hmod : ∀ v, v < 2 ^ n → (hi + v) % 2 ^ n = v := by
    intro v hv
    rw [Nat.add_mod, hhi, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hv]
  unfold encodeInt
  by_cases h : i < prefixMax n
  · simp only [h, ↓reduceIte, List.singleton_append, decodeInt, toNat_toUInt8,
      Nat.mod_eq_of_lt (show hi + i < 256 by omega), hmod i (by omega)]
  · have hv : (hi + prefixMax n) % 2 ^ n = prefixMax n := hmod _ (by omega)
    simp only [h, ↓reduceIte, List.cons_append, decodeInt, toNat_toUInt8,
      Nat.mod_eq_of_lt (show hi + prefixMax n < 256 by omega), hv, Nat.lt_irrefl,
      decodeRest_encodeRest]
    congr 2
    omega

/-- The first octet of an encoded integer carries the flag bits `hi` and the prefix. -/
theorem encodeInt_head {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) : ∃ tl, encodeInt n hi i = (hi + min i (prefixMax n)).toUInt8 :: tl ∧
      (hi + min i (prefixMax n)) < 256 ∧ min i (prefixMax n) < 2 ^ n := by
  have hp := Nat.two_pow_pos n
  have hk : hi + 2 ^ n ≤ 256 := by
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
  have hm : prefixMax n = 2 ^ n - 1 := rfl
  unfold encodeInt
  by_cases h : i < prefixMax n
  · exact ⟨[], by simp [h, Nat.min_eq_left (Nat.le_of_lt h)], by omega, by omega⟩
  · exact ⟨encodeRest (i - prefixMax n), by simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)],
      by omega, by omega⟩

theorem flags_encodeInt_head {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) : ∃ b tl, encodeInt n hi i = b :: tl ∧ flags n b = hi := by
  obtain ⟨tl, he, hlt, hv⟩ := encodeInt_head hn8 hhi hhi' i
  refine ⟨_, tl, he, ?_⟩
  obtain ⟨k, rfl⟩ : 2 ^ n ∣ hi := Nat.dvd_of_mod_eq_zero hhi
  have hp := Nat.two_pow_pos n
  simp only [flags, toNat_toUInt8, Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hv, Nat.add_zero, Nat.mul_comm]

theorem decodeString_encodeString (s rest : List UInt8) :
    decodeString (encodeString s ++ rest) = some (s, rest) := by
  obtain ⟨tl, he, hlt, _⟩ := encodeInt_head (n := 7) (hi := 0) (by decide) (by decide)
    (by decide) s.length
  have hd := decodeInt_encodeInt (n := 7) (hi := 0) (by decide) (by decide) (by decide)
    s.length (s ++ rest)
  have hm : prefixMax 7 = 127 := rfl
  rw [hm] at hlt
  unfold encodeString
  rw [List.append_assoc]
  rw [he] at hd ⊢
  rw [hm] at hd
  simp only [List.cons_append, decodeString, toNat_toUInt8, hm, Nat.mod_eq_of_lt hlt]
  rw [← List.cons_append, hd]
  simp only [Nat.zero_add, show ¬ (128 ≤ min s.length 127) by omega, ↓reduceIte,
    List.length_append, Nat.le_add_right, List.take_left', List.drop_left']

end Silmaril.Proofs.Net.Hpack
