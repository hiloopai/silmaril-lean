module

public import Silmaril.Net.Wire.Defs

/-!
# Network byte order: proofs of the `k`-octet lemmas

For `Silmaril.Net.Wire.Thms` (`beBytes`, `beValue`).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Wire

open Silmaril.Net.Wire

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem toUInt8_eq_of_toNat {n : Nat} {b : UInt8} (h : n % 256 = b.toNat) : n.toUInt8 = b := by
  apply UInt8.toNat_inj.1
  rw [toNat_toUInt8, h]

theorem foldl_beValue (acc : Nat) (xs : List UInt8) :
    xs.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ xs.length + beValue xs := by
  induction xs generalizing acc with
  | nil => simp [beValue]
  | cons b bs ih =>
    simp only [beValue, List.foldl_cons, Nat.zero_mul, Nat.zero_add] at *
    rw [ih, ih b.toNat, List.length_cons, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm 256 (256 ^ bs.length)]

theorem beValue_cons (b : UInt8) (xs : List UInt8) :
    beValue (b :: xs) = b.toNat * 256 ^ xs.length + beValue xs := by
  have := foldl_beValue b.toNat xs
  simp only [beValue, List.foldl_cons, Nat.zero_mul, Nat.zero_add] at *
  exact this

theorem length_beBytes (k x : Nat) : (beBytes k x).length = k := by
  induction k <;> simp [beBytes, *]

theorem beValue_beBytes_mod (k x : Nat) : beValue (beBytes k x) = x % 256 ^ k := by
  induction k with
  | zero => simp [beBytes, beValue, Nat.mod_one]
  | succ k ih =>
    rw [beBytes, beValue_cons, ih, length_beBytes, toNat_toUInt8, Nat.mod_pow_succ,
      Nat.mod_mod]
    rw [Nat.mul_comm (256 ^ k)]
    omega

theorem beValue_beBytes (k x : Nat) (hx : x < 256 ^ k) : beValue (beBytes k x) = x := by
  rw [beValue_beBytes_mod, Nat.mod_eq_of_lt hx]

theorem beValue_lt (xs : List UInt8) : beValue xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [beValue]
  | cons b bs ih =>
    rw [beValue_cons, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt
    have h1 : b.toNat * 256 ^ bs.length ≤ 255 * 256 ^ bs.length := Nat.mul_le_mul_right _ (by omega)
    omega

theorem beBytes_mod (k x : Nat) : beBytes k (x % 256 ^ k) = beBytes k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [beBytes]
    congr 1
    · congr 1
      have hp : 0 < 256 ^ k := Nat.pow_pos (by decide : 0 < 256)
      rw [Nat.mod_pow_succ, Nat.add_comm, Nat.mul_add_div hp,
        Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.add_zero, Nat.mod_mod]
    · rw [← ih (x % 256 ^ (k + 1)), Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow _ (by omega)), ih]

theorem beBytes_beValue (xs : List UInt8) : beBytes xs.length (beValue xs) = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have hlt := beValue_lt bs
    have hb := b.toNat_lt
    rw [List.length_cons, beBytes, beValue_cons]
    congr 1
    · apply toUInt8_eq_of_toNat
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 256)),
        Nat.div_eq_of_lt hlt]
      omega
    · conv => rhs; rw [← ih]
      rw [← beBytes_mod, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]


end Silmaril.Proofs.Net.Wire
