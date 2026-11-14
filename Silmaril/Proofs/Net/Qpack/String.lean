module

public import Silmaril.Net.Qpack.String.Defs
public import Silmaril.Proofs.Net.Qpack.Integer

/-!
# QPACK N-bit prefix string literals: proofs

For `Silmaril.Net.Qpack.String.Thms` (RFC 9204 §4.1.2).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Qpack

open Silmaril.Net.Qpack
open Silmaril.Net.Hpack (encodeInt decodeInt encodeString decodeString)

/-- An encoded `n`-bit prefix string literal followed by `rest`: its first octet lies in
`[hi, hi + 2^(n-1))` (so its `H` bit is clear) and the decoder reads the string back. -/
theorem encodeStringN_split {n hi : Nat} (hn1 : 1 ≤ n) (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0)
    (hhi' : hi < 256) (s rest : List UInt8) : ∃ b tl, encodeStringN n hi s ++ rest = b :: tl ∧
      hi ≤ b.toNat ∧ b.toNat < hi + 2 ^ (n - 1) ∧ decodeStringN n (b :: tl) = some (s, rest) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hdvd : 2 ^ m ∣ 2 ^ (m + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ m)
  have hhi2 : hi % 2 ^ m = 0 := by rw [← Nat.mod_mod_of_dvd hi hdvd, hhi, Nat.zero_mod]
  obtain ⟨b, tl, he, h1, h2, hd⟩ :=
    encodeInt_split (by omega) hhi2 hhi' s.length (s ++ rest)
  refine ⟨b, tl, ?_, h1, h2, ?_⟩
  · simp only [encodeStringN, Nat.add_sub_cancel, List.append_assoc, he]
  · have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have hr : b.toNat % 2 ^ (m + 1) = b.toNat - hi := by
      have : b.toNat = hi + (b.toNat - hi) := by omega
      rw [this, Nat.add_mod, hhi, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]
    simp only [decodeStringN, Nat.add_sub_cancel, hr, show ¬ (2 ^ m ≤ b.toNat - hi) by omega,
      ↓reduceIte, hd, List.length_append, Nat.le_add_right, List.take_left', List.drop_left']

theorem decodeStringN_encodeStringN {n hi : Nat} (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256) (s rest : List UInt8) :
    decodeStringN n (encodeStringN n hi s ++ rest) = some (s, rest) := by
  obtain ⟨b, tl, he, -, -, hd⟩ := encodeStringN_split hn1 hn8 hhi hhi' s rest
  rw [he, hd]

theorem encodeStringN_eight (s : List UInt8) : encodeStringN 8 0 s = encodeString s := rfl

theorem decodeStringN_eight (xs : List UInt8) : decodeStringN 8 xs = decodeString xs := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    have hb : b.toNat % 2 ^ 8 = b.toNat := Nat.mod_eq_of_lt b.toNat_lt
    simp only [decodeStringN, decodeString, Nat.reduceSub, Nat.reducePow] at hb ⊢
    rw [hb]
    split
    · rfl
    · cases decodeInt 7 (b :: bs) <;> rfl

theorem encodeStringN_ne_nil (n hi : Nat) (s : List UInt8) : encodeStringN n hi s ≠ [] := by
  simp [encodeStringN, encodeInt_ne_nil]

end Silmaril.Proofs.Net.Qpack
