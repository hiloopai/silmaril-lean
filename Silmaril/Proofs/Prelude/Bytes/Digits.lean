module

public import Silmaril.Prelude.Bytes.Digits.Defs
import Init.Omega

/-! Proofs for `Silmaril.Prelude.Bytes.Digits.Thms` (and the leaf cases of
`Silmaril.Prelude.Bytes.Thms`). -/

@[expose] public section

namespace Silmaril.Proofs.Prelude.Bytes

open Silmaril.KBytes

/-! ## Digits -/

theorem length_unpack : ∀ k v, (unpack k v).length = k
  | 0, _ => rfl
  | k + 1, v => by simp [unpack, length_unpack k]

theorem pow256 (k : Nat) : 2 ^ (8 * k) = 256 ^ k := by
  rw [Nat.pow_mul]

theorem unpack_mod : ∀ k v, unpack k (v % 256 ^ k) = unpack k v
  | 0, _ => rfl
  | k + 1, v => by
    have h1 : UInt8.ofNat (v % 256 ^ (k + 1)) = UInt8.ofNat v := by
      have : v % 256 ^ (k + 1) % 256 = v % 256 := by
        rw [Nat.pow_succ, Nat.mod_mul_left_mod]
      apply UInt8.toNat.inj
      simpa using this
    have h2 : v % 256 ^ (k + 1) / 256 = v / 256 % 256 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul_right_div_self]
    simp only [unpack, h1, h2, unpack_mod k]

theorem leVal_unpack : ∀ k v, leVal (unpack k v) = v % 256 ^ k
  | 0, v => by simp [unpack, leVal, Nat.mod_one]
  | k + 1, v => by
    simp only [unpack, leVal, leVal_unpack k]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
    simp

theorem unpack_leVal : ∀ bs : List UInt8, unpack bs.length (leVal bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.toNat_lt
    have hdiv : (b.toNat + 256 * leVal bs) / 256 = leVal bs := by omega
    have hbyte : UInt8.ofNat (b.toNat + 256 * leVal bs) = b := by
      apply UInt8.toNat.inj
      simp only [UInt8.toNat_ofNat']
      omega
    simp only [List.length_cons, unpack, leVal, hbyte, hdiv, unpack_leVal bs]

theorem leVal_append : ∀ xs ys : List UInt8,
    leVal (xs ++ ys) = leVal xs + 256 ^ xs.length * leVal ys
  | [], ys => by simp [leVal]
  | x :: xs, ys => by
    simp only [List.cons_append, leVal, leVal_append xs ys, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.mul_comm (256 ^ xs.length) 256, Nat.mul_assoc]
    omega

theorem drop_unpack : ∀ k v i, (unpack k v).drop i = unpack (k - i) (v / 256 ^ i)
  | k, v, 0 => by simp
  | 0, v, i + 1 => by simp [unpack]
  | k + 1, v, i + 1 => by
    rw [unpack, List.drop_succ_cons, drop_unpack k (v / 256) i, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm (256 ^ i) 256]
    simp

theorem take_unpack : ∀ k v j, (unpack k v).take j = unpack (min j k) v
  | k, v, 0 => by simp [unpack]
  | 0, v, j + 1 => by simp [unpack]
  | k + 1, v, j + 1 => by
    rw [unpack, List.take_succ_cons, take_unpack k (v / 256) j, Nat.add_min_add_right, unpack]

theorem leVal_inj {xs ys : List UInt8} (hl : xs.length = ys.length) (h : leVal xs = leVal ys) :
    xs = ys := by
  rw [← unpack_leVal xs, ← unpack_leVal ys, hl, h]

theorem unpack_add (a b v : Nat) : unpack (a + b) v = unpack a (v % 256 ^ a) ++ unpack b (v / 256 ^ a) := by
  rw [unpack_mod, ← List.take_append_drop a (unpack (a + b) v), take_unpack, drop_unpack,
    Nat.min_eq_left (by omega), Nat.add_sub_cancel_left]

theorem unpackFast_eq : ∀ k v, unpackFast k v = unpack k v := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro v
    rw [unpackFast]
    split
    · rfl
    · rw [ih (k / 2) (by omega), ih (k - k / 2) (by omega), ← unpack_add,
        show k / 2 + (k - k / 2) = k by omega]

end Silmaril.Proofs.Prelude.Bytes
