module

public import Silmaril.Net.Quic.VarInt.Defs

/-!
# QUIC variable-length integers: proofs

Round trips, bounds and the append law for RFC 9000 §16, for
`Silmaril.Net.Quic.VarInt.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.VarInt

open Silmaril.Net.Quic.VarInt

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem beBytes_length (k x : Nat) : (beBytes k x).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [beBytes, ih]

theorem beValueFrom_cons (acc : Nat) (b : UInt8) (bs : List UInt8) :
    beValueFrom acc (b :: bs) = beValueFrom (acc * 256 + b.toNat) bs := rfl

theorem beValueFrom_beBytes (k : Nat) : ∀ acc x : Nat,
    beValueFrom acc (beBytes k x) = acc * 256 ^ k + x % 256 ^ k := by
  induction k with
  | zero => intro acc x; simp [beBytes, beValueFrom, Nat.mod_one]
  | succ k ih =>
    intro acc x
    rw [beBytes, beValueFrom_cons, ih, toNat_toUInt8, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
      Nat.mod_pow_succ, Nat.pow_succ]
    generalize 256 ^ k = B
    generalize x / B % 256 = q
    have : acc * (B * 256) = acc * 256 * B := by
      rw [Nat.mul_comm B 256, ← Nat.mul_assoc]
    rw [Nat.add_mul, this, Nat.mul_comm B q]
    omega

theorem beValueFrom_shift (ys : List UInt8) : ∀ acc : Nat,
    beValueFrom acc ys = acc * 256 ^ ys.length + beValueFrom 0 ys := by
  induction ys with
  | nil => intro acc; simp [beValueFrom]
  | cons y ys ih =>
    intro acc
    rw [beValueFrom_cons, beValueFrom_cons, ih, ih (0 * 256 + y.toNat)]
    simp only [List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ ys.length)]
    omega

theorem beValueFrom_zero_lt (ys : List UInt8) : beValueFrom 0 ys < 256 ^ ys.length := by
  induction ys with
  | nil => simp [beValueFrom]
  | cons y ys ih =>
    rw [beValueFrom_cons, beValueFrom_shift, List.length_cons, Nat.pow_succ]
    have hy := y.toNat_lt
    simp only [Nat.zero_mul, Nat.zero_add]
    have : y.toNat * 256 ^ ys.length + 256 ^ ys.length ≤ 256 * 256 ^ ys.length := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hy
    rw [Nat.mul_comm (256 ^ ys.length) 256]
    omega

theorem prefixOf_lt (k : Nat) : prefixOf k < 4 := by
  unfold prefixOf; split <;> decide

theorem lengthOfPrefix_prefixOf {k : Nat} (hk : k ∈ lengths) : lengthOfPrefix (prefixOf k) = k := by
  simp only [lengths, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> rfl

theorem lengths_pos {k : Nat} (hk : k ∈ lengths) : 1 ≤ k := by
  simp only [lengths, List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

theorem decode_encodeWith {k v : Nat} (h : FitsIn k v) (rest : List UInt8) :
    decode (encodeWith k v ++ rest) = some (v, rest) := by
  obtain ⟨hk, hv⟩ := h
  have hp := prefixOf_lt k
  have hq : v / 256 ^ (k - 1) < 64 := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2 hv
  generalize hq' : v / 256 ^ (k - 1) = q at hq
  have hb : (prefixOf k * 64 + q % 64).toUInt8.toNat = prefixOf k * 64 + q := by
    rw [toNat_toUInt8, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (prefixOf k * 64 + q) / 64 = prefixOf k := by omega
  have hmod : (prefixOf k * 64 + q) % 64 = q := by omega
  simp only [encodeWith, hq', List.cons_append, decode, hb, hdiv, hmod, lengthOfPrefix_prefixOf hk,
    List.length_append, beBytes_length, show ¬ (k - 1 + rest.length < k - 1) by omega, ↓reduceIte,
    List.take_left' (beBytes_length _ _), List.drop_left' (beBytes_length _ _), beValueFrom_beBytes,
    Option.some.injEq, Prod.mk.injEq, and_true]
  rw [← hq']
  exact Nat.div_add_mod' v _

theorem lenOf_fits {v : Nat} (h : Valid v) : FitsIn (lenOf v) v := by
  unfold Valid maxValue at h
  unfold lenOf FitsIn lengths
  split
  · exact ⟨by simp, by simp; omega⟩
  · split
    · exact ⟨by simp, by simp; omega⟩
    · split
      · exact ⟨by simp, by simp; omega⟩
      · exact ⟨by simp, by simp; omega⟩

theorem decode_encode {v : Nat} (h : Valid v) (rest : List UInt8) :
    decode (encode v ++ rest) = some (v, rest) :=
  decode_encodeWith (lenOf_fits h) rest

theorem encodeWith_length (k v : Nat) : (encodeWith k v).length = 1 + (k - 1) := by
  simp [encodeWith, beBytes_length, Nat.add_comm]

theorem lenOf_mem (v : Nat) : lenOf v ∈ lengths := by
  unfold lenOf lengths; split <;> (try split) <;> (try split) <;> simp

theorem encode_length (v : Nat) : (encode v).length = lenOf v := by
  have := lengths_pos (lenOf_mem v)
  rw [encode, encodeWith_length]; omega

theorem lengthOfPrefix_le (p : Nat) : 1 ≤ lengthOfPrefix p ∧ lengthOfPrefix p ≤ 8 := by
  unfold lengthOfPrefix
  have : p % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (show p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 by omega) with h | h | h | h <;>
    simp [h]

theorem decode_eq_some {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) :
    ∃ b ys, xs = b :: (ys ++ rest) ∧ ys.length = lengthOfPrefix (b.toNat / 64) - 1 ∧
      v = beValueFrom (b.toNat % 64) ys := by
  match xs, h with
  | b :: tl, h =>
    simp only [decode] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨b, tl.take (lengthOfPrefix (b.toNat / 64) - 1), ?_, ?_, rfl⟩
      · simp
      · simp only [List.length_take]; omega

theorem decode_lt {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : v < 2 ^ 62 := by
  obtain ⟨b, ys, -, hlen, rfl⟩ := decode_eq_some h
  rw [beValueFrom_shift]
  have h1 := beValueFrom_zero_lt ys
  have hb : b.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have hk := lengthOfPrefix_le (b.toNat / 64)
  have hpow : 256 ^ ys.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have : b.toNat % 64 * 256 ^ ys.length + beValueFrom 0 ys < 64 * 256 ^ ys.length := by
    have : (b.toNat % 64 + 1) * 256 ^ ys.length ≤ 64 * 256 ^ ys.length :=
      Nat.mul_le_mul_right _ hb
    rw [Nat.succ_mul] at this; omega
  have : 64 * 256 ^ ys.length ≤ 64 * 256 ^ 7 := Nat.mul_le_mul_left _ hpow
  have : (64 * 256 ^ 7 : Nat) = 2 ^ 62 := by decide
  omega

theorem decode_valid {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : Valid v := by
  have := decode_lt h; unfold Valid maxValue; omega

theorem decode_local {xs : List UInt8} {v : Nat} {rest : List UInt8} (tail : List UInt8)
    (h : decode xs = some (v, rest)) : decode (xs ++ tail) = some (v, rest ++ tail) := by
  obtain ⟨b, ys, rfl, hlen, rfl⟩ := decode_eq_some h
  simp only [List.cons_append, decode, List.append_assoc, List.length_append, hlen,
    show ¬ (lengthOfPrefix (b.toNat / 64) - 1 + (rest.length + tail.length) <
      lengthOfPrefix (b.toNat / 64) - 1) by omega, ↓reduceIte, List.take_left' hlen,
    List.drop_left' hlen]

theorem decode_length {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : rest.length < xs.length := by
  obtain ⟨b, ys, rfl, -, -⟩ := decode_eq_some h
  simp; omega

theorem decode_suffix {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : rest <:+ xs := by
  obtain ⟨b, ys, rfl, -, -⟩ := decode_eq_some h
  exact ⟨b :: ys, by simp⟩

theorem decodeAllFuel_flatMap (vs : List Nat) (hv : ∀ v ∈ vs, Valid v) :
    ∀ fuel, (vs.flatMap encode).length ≤ fuel → decodeAllFuel fuel (vs.flatMap encode) = some vs := by
  induction vs with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons v vs ih =>
    intro fuel hf
    have hvv : Valid v := hv v (by simp)
    have hlen : 1 ≤ (encode v).length := by
      rw [encode_length]; exact lengths_pos (lenOf_mem v)
    simp only [List.flatMap_cons, List.length_append] at hf ⊢
    obtain ⟨b, tl, hbt⟩ : ∃ b tl, encode v = b :: tl := by
      cases h : encode v with
      | nil => rw [h] at hlen; simp at hlen
      | cons b tl => exact ⟨b, tl, rfl⟩
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      have hd := decode_encode hvv (vs.flatMap encode)
      rw [hbt, List.cons_append] at hd ⊢
      simp only [decodeAllFuel, hd, ih (fun w hw => hv w (by simp [hw])) fuel (by omega),
        Option.map_some]

theorem decodeAll_flatMap (vs : List Nat) (hv : ∀ v ∈ vs, Valid v) :
    decodeAll (vs.flatMap encode) = some vs :=
  decodeAllFuel_flatMap vs hv _ (Nat.le_refl _)

end Silmaril.Proofs.Net.Quic.VarInt
