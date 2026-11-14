module

public import Silmaril.Net.WebSocket.Frame.Defs
public import Silmaril.Net.Wire.Thms

/-!
# WebSocket frames: proofs

For `Silmaril.Net.WebSocket.Frame.Thms` (RFC 6455 §5.2, §5.3, §5.5.1).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebSocket

open Silmaril.Net.WebSocket
open Silmaril.Net.Wire (beBytes beValue)

/-! ## Masking -/

theorem at_mod (k : MaskKey) (j : Nat) : k.at (j % 4) = k.at j := by
  simp only [MaskKey.at, Nat.mod_mod]

theorem applyMask_applyMask (k : MaskKey) (off : Nat) (xs : List UInt8) :
    applyMask k off (applyMask k off xs) = xs := by
  induction xs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    simp only [applyMask, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero, ih]

theorem length_applyMask (k : MaskKey) (off : Nat) (xs : List UInt8) :
    (applyMask k off xs).length = xs.length := by
  induction xs generalizing off with
  | nil => rfl
  | cons b bs ih => simp only [applyMask, List.length_cons, ih]

theorem applyMask_append (k : MaskKey) (off : Nat) (xs ys : List UInt8) :
    applyMask k off (xs ++ ys) = applyMask k off xs ++ applyMask k (off + xs.length) ys := by
  induction xs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append, applyMask, ih, List.length_cons,
      show off + (bs.length + 1) = off + 1 + bs.length by omega]

theorem applyMask_mod (k : MaskKey) (off : Nat) (xs : List UInt8) :
    applyMask k (off % 4) xs = applyMask k off xs := by
  induction xs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    simp only [applyMask, at_mod]
    rw [← ih (off + 1), ← ih (off % 4 + 1)]
    congr 2
    omega

theorem maskWith_maskWith (k : Option MaskKey) (xs : List UInt8) :
    maskWith k (maskWith k xs) = xs := by
  cases k <;> simp [maskWith, applyMask_applyMask]

theorem length_maskWith (k : Option MaskKey) (xs : List UInt8) :
    (maskWith k xs).length = xs.length := by
  cases k <;> simp [maskWith, length_applyMask]

/-! ## Big-endian lengths -/

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.1
  rw [toNat_toUInt8]
  have := b.toNat_lt
  omega

theorem toUInt8_eq_of_toNat {n : Nat} {b : UInt8} (h : n % 256 = b.toNat) : n.toUInt8 = b := by
  apply UInt8.toNat_inj.1
  rw [toNat_toUInt8, h]

theorem beValue_beBytes2 (x : Nat) (hx : x < 2 ^ 16) : beValue (beBytes 2 x) = x :=
  Silmaril.Net.Wire.beValue_beBytes 2 x (by simpa using hx)

theorem beValue_beBytes8 (x : Nat) (hx : x < 2 ^ 64) : beValue (beBytes 8 x) = x :=
  Silmaril.Net.Wire.beValue_beBytes 8 x (by simpa using hx)

theorem beValue2 (a b : UInt8) : beValue [a, b] = a.toNat * 256 + b.toNat := by
  simp [beValue]

theorem beBytes_beValue2 (a b : UInt8) : beBytes 2 (beValue [a, b]) = [a, b] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [beBytes, beValue2, List.cons.injEq, and_true, Nat.reducePow]
  constructor <;> apply toUInt8_eq_of_toNat <;> omega

theorem beBytes_beValue8 (a b c d e f g h : UInt8) :
    beBytes 8 (beValue [a, b, c, d, e, f, g, h]) = [a, b, c, d, e, f, g, h] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have he := e.toNat_lt
  have hf := f.toNat_lt
  have hg := g.toNat_lt
  have hh := h.toNat_lt
  simp only [beBytes, beValue, List.foldl, List.cons.injEq, and_true, Nat.reducePow,
    Nat.zero_mul, Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply toUInt8_eq_of_toNat <;> omega

theorem beValue_lt8 (xs : List UInt8) (h : xs.length = 8) : beValue xs < 2 ^ 64 := by
  match xs, h with
  | [a, b, c, d, e, f, g, h], _ =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    have hd := d.toNat_lt
    have he := e.toNat_lt
    have hf := f.toNat_lt
    have hg := g.toNat_lt
    have hh := h.toNat_lt
    simp only [beValue, List.foldl, Nat.reducePow, Nat.zero_mul, Nat.zero_add]
    omega

/-! ## The length field -/

theorem lengthCode_lt (n : Nat) : (lengthCode n).1 < 128 := by
  unfold lengthCode; split
  · simp only; omega
  · split <;> simp

theorem readLength_lengthCode (n : Nat) (hn : n < maxLength) (ys : List UInt8) :
    readLength (lengthCode n).1 ((lengthCode n).2 ++ ys) = .ok (n, ys) := by
  unfold lengthCode readLength maxLength at *
  by_cases h1 : n ≤ 125
  · simp [h1]
  · by_cases h2 : n < 65536
    · simp only [h1, h2, ↓reduceIte, show ¬ (126 ≤ 125) by omega, List.length_append,
        show (beBytes 2 n).length = 2 from rfl, show ¬ (2 + ys.length < 2) by omega,
        List.take_left' (show (beBytes 2 n).length = 2 from rfl),
        List.drop_left' (show (beBytes 2 n).length = 2 from rfl),
        beValue_beBytes2 n (by omega)]
    · have h8 : (beBytes 8 n).length = 8 := rfl
      simp only [h1, h2, ↓reduceIte, show ¬ (127 ≤ 125) by omega, show ¬ (127 = 126) by omega,
        List.length_append, h8, show ¬ (8 + ys.length < 8) by omega,
        List.take_left' h8, List.drop_left' h8, beValue_beBytes8 n (by omega)]
      simp only [show ¬ (2 ^ 63 ≤ n) by omega, ↓reduceIte]

theorem readLength_sound {c : Nat} {ys zs : List UInt8} {n : Nat}
    (h : readLength c ys = .ok (n, zs)) (hc : c < 128) :
    n < maxLength ∧ (lengthCode n).1 = c ∧ ys = (lengthCode n).2 ++ zs := by
  unfold readLength at h
  split at h
  · next h1 =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [lengthCode, h1, maxLength]
    omega
  · next h1 =>
    split at h
    · next h2 =>
      split at h
      · cases h
      · match ys with
        | a :: b :: rest =>
          simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons,
            List.drop_zero] at h
          split at h
          · cases h
          · next h3 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hlt : beValue [a, b] < 65536 := by
              have := a.toNat_lt; have := b.toNat_lt; rw [beValue2]; omega
            refine ⟨by unfold maxLength; omega, ?_, ?_⟩
            · simp [lengthCode, h3, hlt, h2]
            · simp only [lengthCode, h3, hlt, ↓reduceIte, beBytes_beValue2, List.cons_append,
                List.nil_append]
        | [] | [_] => simp at *
    · next h2 =>
      split at h
      · cases h
      · match ys with
        | a :: b :: c' :: d :: e :: f :: g :: hh :: rest =>
          simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons,
            List.drop_zero] at h
          split at h
          · cases h
          · next h3 =>
            split at h
            · cases h
            · next h4 =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨by omega, ?_, ?_⟩
              · simp only [lengthCode, show ¬ (beValue [a, b, c', d, e, f, g, hh] ≤ 125) by omega,
                  h4, ↓reduceIte]
                omega
              · simp only [lengthCode, show ¬ (beValue [a, b, c', d, e, f, g, hh] ≤ 125) by omega,
                  h4, ↓reduceIte, beBytes_beValue8, List.cons_append, List.nil_append]
        | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
        | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] => simp at *

/-! ## The first two octets -/

theorem byte0_fields (f : Frame) (hv : f.Valid) :
    ((byte0 f).toNat / 128 == 1) = f.fin ∧ (byte0 f).toNat / 16 % 8 = f.rsv ∧
      (byte0 f).toNat % 16 = f.opcode := by
  obtain ⟨hr, ho, -⟩ := hv
  unfold byte0
  rw [toNat_toUInt8]
  cases f.fin <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> refine ⟨?_, ?_, ?_⟩ <;>
    first | omega | (simp only [beq_iff_eq, beq_eq_false_iff_ne]; omega)

theorem byte1_fields (m : Bool) (c : Nat) (hc : c < 128) :
    (((if m then 128 else 0) + c).toUInt8.toNat % 128 = c) ∧
      ((((if m then 128 else 0) + c).toUInt8.toNat / 128 == 1) = m) := by
  rw [toNat_toUInt8]
  cases m <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> refine ⟨by omega, ?_⟩ <;>
    simp only [beq_iff_eq, beq_eq_false_iff_ne] <;> omega

theorem byte0_of (b : UInt8) {k : Option MaskKey} {p : List UInt8} :
    byte0 ⟨b.toNat / 128 == 1, b.toNat / 16 % 8, b.toNat % 16, k, p⟩ = b := by
  unfold byte0
  apply toUInt8_eq_of_toNat
  have := b.toNat_lt
  simp only
  by_cases h : b.toNat / 128 = 1
  · simp only [h, BEq.rfl, Bool.toNat_true]; omega
  · have h0 : b.toNat / 128 = 0 := by omega
    simp only [h0, Bool.toNat_false, show ((0 : Nat) == 1) = false from rfl]; omega

theorem byte1_of (b : UInt8) :
    ((if (b.toNat / 128 == 1) then 128 else 0) + b.toNat % 128).toUInt8 = b := by
  apply toUInt8_eq_of_toNat
  have := b.toNat_lt
  by_cases h : b.toNat / 128 = 1
  · simp only [h, BEq.rfl, ↓reduceIte]; omega
  · have h0 : b.toNat / 128 = 0 := by omega
    simp only [h0, show ((0 : Nat) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega

/-! ## Round trip and unambiguity -/

theorem readKey_enc (k : Option MaskKey) (ys : List UInt8) :
    readKey k.isSome ((k.map MaskKey.bytes).getD [] ++ ys) = some (k, ys) := by
  cases k <;> rfl

theorem readKey_sound {m : Bool} {ys zs : List UInt8} {k : Option MaskKey}
    (h : readKey m ys = some (k, zs)) : k.isSome = m ∧ ys = (k.map MaskKey.bytes).getD [] ++ zs := by
  unfold readKey at h
  cases m
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · simp only [↓reduceIte] at h
    match ys, h with
    | a :: b :: c :: d :: rest, h =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [MaskKey.bytes]

theorem decode_encode (m : Nat) (f : Frame) (hv : f.Valid) (hm : f.payload.length ≤ m)
    (rest : List UInt8) : decode m (encode f ++ rest) = .ok (f, rest) := by
  have hv' := hv
  obtain ⟨-, -, hl⟩ := hv'
  obtain ⟨hfin, hrsv, hop⟩ := byte0_fields f hv
  obtain ⟨hb1, hb1'⟩ := byte1_fields f.mask.isSome _ (lengthCode_lt f.payload.length)
  simp only [encode, List.cons_append, decode, hb1, hb1', List.append_assoc]
  rw [readLength_lengthCode _ hl]
  simp only [show ¬ (m < f.payload.length) by omega, ↓reduceIte]
  rw [readKey_enc]
  simp only [List.length_append, length_maskWith, show ¬ (f.payload.length + rest.length <
    f.payload.length) by omega, ↓reduceIte, List.take_left' (length_maskWith _ _),
    List.drop_left' (length_maskWith _ _), maskWith_maskWith, hfin, hrsv, hop]

theorem decode_sound {m : Nat} {xs : List UInt8} {f : Frame} {rest : List UInt8}
    (h : decode m xs = .ok (f, rest)) :
    f.Valid ∧ f.payload.length ≤ m ∧ xs = encode f ++ rest := by
  match xs with
  | [] | [_] => simp [decode] at h
  | b0 :: b1 :: ys =>
    simp only [decode] at h
    split at h
    · cases h
    · next len ys' hlen =>
      obtain ⟨hlt, hcode, hys⟩ := readLength_sound hlen (Nat.mod_lt _ (by omega))
      split at h
      · cases h
      · next hm =>
        split at h
        · cases h
        · next key zs hkey =>
          obtain ⟨hks, hzs⟩ := readKey_sound hkey
          split at h
          · cases h
          · next hz =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hpl : (maskWith key (zs.take len)).length = len := by
              rw [length_maskWith, List.length_take]; omega
            refine ⟨⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), by
              show (maskWith key (zs.take len)).length < maxLength
              rw [hpl]; exact hlt⟩, by
              show (maskWith key (zs.take len)).length ≤ m
              rw [hpl]; omega, ?_⟩
            simp only [encode, hpl, maskWith_maskWith, hcode, hks, byte0_of, byte1_of,
              List.cons_append, List.append_assoc, List.take_append_drop, ← hzs, ← hys]

/-! ## Control frames -/

theorem length_encode (f : Frame) :
    (encode f).length = 2 + (lengthCode f.payload.length).2.length +
      (if f.mask.isSome then 4 else 0) + f.payload.length := by
  cases hk : f.mask <;> simp [encode, hk, length_maskWith, MaskKey.bytes] <;> omega

theorem controlOk_length (f : Frame) (h : f.controlOk = true) (hc : isControl f.opcode = true) :
    (encode f).length ≤ 131 := by
  simp only [Frame.controlOk, hc, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rw [length_encode]
  have : (lengthCode f.payload.length).2 = [] := by simp [lengthCode, h.2]
  rw [this]
  split <;> simp <;> omega

/-! ## Close bodies -/

theorem decodeClose_encodeClose (c : Option (Nat × List UInt8)) (hv : CloseBody.Valid c) :
    decodeClose (encodeClose c) = some c := by
  match c, hv with
  | none, _ => rfl
  | some (code, reason), ⟨hc, hu⟩ =>
    have hlt : code < 2 ^ 16 := by
      simp only [isSendableCloseCode, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    have e : beBytes 2 code = [(code / 256 % 256).toUInt8, (code % 256).toUInt8] := by
      simp [beBytes]
    simp only [encodeClose, e, List.cons_append, List.nil_append, decodeClose]
    have hv : beValue [(code / 256 % 256).toUInt8, (code % 256).toUInt8] = code := by
      rw [← e]; exact beValue_beBytes2 code hlt
    simp [hv, hc, hu]

theorem decodeClose_sound {b : List UInt8} {c : Option (Nat × List UInt8)}
    (h : decodeClose b = some c) : encodeClose c = b ∧ CloseBody.Valid c := by
  match b with
  | [] => simp only [decodeClose, Option.some.injEq] at h; subst h; exact ⟨rfl, trivial⟩
  | [_] => simp [decodeClose] at h
  | a :: b' :: reason =>
    simp only [decodeClose] at h
    split at h
    · next hok =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hok
      exact ⟨by simp only [encodeClose, beBytes_beValue2, List.cons_append, List.nil_append],
        hok.1, hok.2⟩
    · cases h

end Silmaril.Proofs.Net.WebSocket
