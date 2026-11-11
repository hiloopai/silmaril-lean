module

public import Silmaril.Wasm.Tools.Meta.Leb.Defs

/-!
# `var_u32`: the reader inverts the minimal encoder
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- `n` split into its low seven bits and the rest, scaled by `p`. -/
theorem mul_split128 (n p : Nat) : n * p = n % 128 * p + n / 128 * (p * 128) := by
  conv => lhs; rw [← Nat.mod_add_div n 128]
  rw [Nat.add_mul, Nat.mul_comm 128 (n / 128), Nat.mul_assoc, Nat.mul_comm 128 p]

theorem toNat_toUInt8_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8]; omega

/-- The continuation reader on a minimal encoding. -/
theorem readU32Go_encU32 (n : Nat) : ∀ (acc s : Nat) (rest : List UInt8), 7 ≤ s → s ≤ 28 →
    s % 7 = 0 → n * 2 ^ s < 2 ^ 32 →
    readU32Go acc s (encU32 n ++ rest) = .ok (acc + n * 2 ^ s, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    show ∀ (acc s : Nat) (rest : List UInt8), 7 ≤ s → s ≤ 28 → s % 7 = 0 → n * 2 ^ s < 2 ^ 32 →
      readU32Go acc s (encU32 n ++ rest) = .ok (acc + n * 2 ^ s, rest)
    intro acc s rest h7 h28 hmod hlt
    show readU32Go acc s (encU32 n ++ rest) = .ok (acc + n * 2 ^ s, rest)
    by_cases hn : n < 128
    · show readU32Go acc s (encU32 n ++ rest) = .ok (acc + n * 2 ^ s, rest)
      have hb : (n.toUInt8).toNat = n := toNat_toUInt8_of_lt (by omega)
      have hsmall : 25 ≤ s → n < 16 := by
        intro h25
        have hs : s = 28 := by omega
        subst hs
        have : n * 2 ^ 28 < 16 * 2 ^ 28 := by simpa using hlt
        exact Nat.lt_of_mul_lt_mul_right this
      have hchk : ¬ (25 ≤ s ∧ n / 2 ^ (32 - s) ≠ 0) := by
        rintro ⟨h25, hne⟩
        have hs : s = 28 := by omega
        subst hs
        exact hne (Nat.div_eq_of_lt (by have := hsmall h25; simpa using this))
      rw [encU32]
      simp only [hn, ↓reduceIte, List.cons_append, List.nil_append, readU32Go, hb, hchk, ↓reduceIte,
        Nat.mod_eq_of_lt hn]
    · show readU32Go acc s (encU32 n ++ rest) = .ok (acc + n * 2 ^ s, rest)
      have hb : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 :=
        toNat_toUInt8_of_lt (by omega)
      have hs : s + 7 ≤ 28 := by
        have h1 : 128 * 2 ^ s ≤ n * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
        have h2 : 2 ^ (s + 7) < 2 ^ 32 := by
          rw [Nat.pow_add]; have : 2 ^ s * 2 ^ 7 = 128 * 2 ^ s := by rw [Nat.mul_comm]
          omega
        have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
        omega
      have hchk : ¬ (25 ≤ s ∧ (n % 128 + 128) / 2 ^ (32 - s) ≠ 0) := by omega
      have hq : n / 128 < n := by omega
      have hlt' : n / 128 * 2 ^ (s + 7) < 2 ^ 32 := by
        have : n / 128 * 2 ^ (s + 7) = n / 128 * 128 * 2 ^ s := by
          rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (2 ^ s)]
        rw [this]
        have : n / 128 * 128 ≤ n := Nat.div_mul_le_self n 128
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ this) hlt
      have ih' := ih (n / 128) hq (acc + (n % 128 + 128) % 128 * 2 ^ s) (s + 7) rest (by omega)
        hs (by omega) hlt'
      rw [encU32]
      simp only [hn, ↓reduceIte, List.cons_append, readU32Go, hb, hchk]
      have hge : ¬ (n % 128 + 128 < 128) := by omega
      simp only [hge, ↓reduceIte, ih']
      congr 2
      have hm : (n % 128 + 128) % 128 = n % 128 := by omega
      rw [hm, Nat.pow_add, mul_split128 n (2 ^ s), Nat.add_assoc]

/-- **The reader inverts the minimal encoder** below `2^32`. -/
theorem readU32_encU32 (n : Nat) (rest : List UInt8) (h : n < 2 ^ 32) :
    readU32 (encU32 n ++ rest) = .ok (n, rest) := by
  by_cases hn : n < 128
  · rw [encU32]
    simp only [hn, ↓reduceIte, List.cons_append, List.nil_append, readU32,
      toNat_toUInt8_of_lt (show n < 256 by omega)]
  · have hb : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 :=
      toNat_toUInt8_of_lt (by omega)
    have hge : ¬ (n % 128 + 128 < 128) := by omega
    have hlt' : n / 128 * 2 ^ 7 < 2 ^ 32 := by
      have : n / 128 * 128 ≤ n := Nat.div_mul_le_self n 128
      simp only [show (2:Nat) ^ 7 = 128 from rfl]; omega
    have ih := readU32Go_encU32 (n / 128) ((n % 128 + 128) % 128) 7 rest (by omega) (by omega)
      (by omega) hlt'
    rw [encU32]
    simp only [hn, ↓reduceIte, List.cons_append, readU32, hb, hge, ih]
    congr 2
    have hm : (n % 128 + 128) % 128 = n % 128 := by omega
    rw [hm]
    show n % 128 + n / 128 * 128 = n
    omega

end Silmaril.Wasm.Tools.Meta

end
