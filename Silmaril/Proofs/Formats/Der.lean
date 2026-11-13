module

public import Silmaril.Formats.Der.Defs

/-!
# DER: proofs

For `Silmaril.Formats.Der.Thms` (X.690 §8.1, §8.3, §10.1).
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Der

open Silmaril.Formats.Der

/-! ## Octets and numbers -/

/-- Induction from the right end of a list. -/
theorem concatRec {motive : List UInt8 → Prop} (nil : motive [])
    (append_singleton : ∀ xs b, motive xs → motive (xs ++ [b])) (xs : List UInt8) : motive xs := by
  have : ∀ ys : List UInt8, motive ys.reverse := by
    intro ys
    induction ys with
    | nil => exact nil
    | cons b ys ih => simpa using append_singleton _ b ih
  simpa using this xs.reverse

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.1
  rw [toNat_toUInt8]
  have := b.toNat_lt
  omega

theorem natValue_concat (xs : List UInt8) (b : UInt8) :
    natValue (xs ++ [b]) = natValue xs * 256 + b.toNat := by
  simp [natValue, List.foldl_append]

theorem natValue_lt (xs : List UInt8) : natValue xs < 256 ^ xs.length := by
  induction xs using concatRec with
  | nil => simp [natValue]
  | append_singleton xs b ih =>
    rw [natValue_concat, List.length_append, List.length_singleton, Nat.pow_succ]
    have := b.toNat_lt
    have h : natValue xs * 256 + 256 ≤ 256 ^ xs.length * 256 := by
      have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt ih)
      simpa [Nat.succ_mul] using this
    omega

/-- A minimal non-empty octet string has a value of at least `256 ^ (length - 1)`. -/
theorem natValue_ge {xs : List UInt8} (hm : Minimal xs) (hne : xs ≠ []) :
    256 ^ (xs.length - 1) ≤ natValue xs := by
  induction xs using concatRec with
  | nil => exact absurd rfl hne
  | append_singleton xs b ih =>
    rw [natValue_concat, List.length_append, List.length_singleton, Nat.add_sub_cancel]
    cases xs with
    | nil =>
      simp only [Minimal, List.nil_append, List.head?_cons, ne_eq, Option.some.injEq] at hm
      have : b.toNat ≠ 0 := fun h => hm (UInt8.toNat_inj.1 (by simpa using h))
      simp [natValue]; omega
    | cons c cs =>
      have hm' : Minimal (c :: cs) := by simpa [Minimal] using hm
      have h1 := ih hm' (by simp)
      have hL : (c :: cs).length = cs.length + 1 := rfl
      rw [hL, Nat.add_sub_cancel] at h1
      rw [hL, Nat.pow_succ]
      have h2 := Nat.mul_le_mul_right 256 h1
      generalize 256 ^ cs.length = P at h2 ⊢
      generalize natValue (c :: cs) = V at h2 ⊢
      exact Nat.le_trans h2 (Nat.le_add_right _ _)

theorem natBytesAux_zero (f : Nat) : natBytesAux f 0 = [] := by
  cases f <;> simp [natBytesAux]

theorem natBytesAux_pos {f n : Nat} (hn : n ≠ 0) :
    natBytesAux (f + 1) n = natBytesAux f (n / 256) ++ [(n % 256).toUInt8] := by
  simp [natBytesAux, hn]

/-- The fuel does not matter once it is at least the number. -/
theorem natBytesAux_fuel : ∀ (f g n : Nat), n ≤ f → n ≤ g → natBytesAux f n = natBytesAux g n
  | 0, _, n, hf, _ => by
    have : n = 0 := by omega
    subst this; simp [natBytesAux_zero]
  | _, 0, n, _, hg => by
    have : n = 0 := by omega
    subst this; simp [natBytesAux_zero]
  | f + 1, g + 1, n, hf, hg => by
    by_cases hn : n = 0
    · subst hn; simp [natBytesAux_zero]
    · rw [natBytesAux_pos hn, natBytesAux_pos hn,
        natBytesAux_fuel f g (n / 256) (by omega) (by omega)]

theorem natBytesAux_spec : ∀ (f n : Nat), n ≤ f →
    natValue (natBytesAux f n) = n ∧ Minimal (natBytesAux f n) ∧
      (natBytesAux f n = [] ↔ n = 0)
  | 0, n, h => by
    have : n = 0 := by omega
    subst this; simp [natBytesAux, natValue, Minimal]
  | f + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [natBytesAux_zero, natValue, Minimal]
    · rw [natBytesAux_pos hn]
      obtain ⟨hv, hm, he⟩ := natBytesAux_spec f (n / 256) (by omega)
      refine ⟨?_, ?_, by simp [hn]⟩
      · rw [natValue_concat, hv, toNat_toUInt8]; omega
      · by_cases hq : n / 256 = 0
        · rw [he.2 hq]
          simp only [Minimal, List.nil_append, List.head?_cons, ne_eq, Option.some.injEq]
          intro h0
          have := congrArg UInt8.toNat h0
          rw [toNat_toUInt8] at this
          simp at this; omega
        · obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (fun h => hq (he.1 h))
          rw [hc] at hm ⊢
          simpa [Minimal] using hm

theorem natValue_natBytes (n : Nat) : natValue (natBytes n) = n :=
  (natBytesAux_spec n n (Nat.le_refl _)).1

theorem minimal_natBytes (n : Nat) : Minimal (natBytes n) :=
  (natBytesAux_spec n n (Nat.le_refl _)).2.1

theorem natBytes_eq_nil (n : Nat) : natBytes n = [] ↔ n = 0 :=
  (natBytesAux_spec n n (Nat.le_refl _)).2.2

theorem natBytes_concat (n : Nat) (hn : n ≠ 0) :
    natBytes n = natBytes (n / 256) ++ [(n % 256).toUInt8] := by
  unfold natBytes
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [natBytesAux_pos hn, natBytesAux_fuel m ((m + 1) / 256) _ (by omega) (Nat.le_refl _)]

theorem natBytes_natValue {xs : List UInt8} (hm : Minimal xs) : natBytes (natValue xs) = xs := by
  induction xs using concatRec with
  | nil => simp [natValue, natBytes, natBytesAux]
  | append_singleton xs b ih =>
    have hb := b.toNat_lt
    cases xs with
    | nil =>
      simp only [Minimal, List.nil_append, List.head?_cons, ne_eq, Option.some.injEq] at hm
      have hb0 : b.toNat ≠ 0 := fun h => hm (UInt8.toNat_inj.1 (by simpa using h))
      have hv : natValue [b] = b.toNat := by simp [natValue]
      simp only [List.nil_append]
      rw [hv, natBytes_concat _ hb0, show b.toNat / 256 = 0 by omega,
        (natBytes_eq_nil 0).2 rfl, Nat.mod_eq_of_lt hb, toUInt8_toNat]
      rfl
    | cons c cs =>
      have hm' : Minimal (c :: cs) := by simpa [Minimal] using hm
      have hge := natValue_ge hm' (by simp)
      have hpos : natValue (c :: cs) ≠ 0 := by
        have := Nat.pow_pos (n := (c :: cs).length - 1) (show 0 < 256 by omega); omega
      rw [natValue_concat, natBytes_concat _ (by omega)]
      rw [show (natValue (c :: cs) * 256 + b.toNat) / 256 = natValue (c :: cs) by omega,
        show (natValue (c :: cs) * 256 + b.toNat) % 256 = b.toNat by omega, ih hm',
        toUInt8_toNat]

theorem length_natBytes_lt {n k : Nat} (h : n < 256 ^ k) : (natBytes n).length ≤ k := by
  by_cases hn : n = 0
  · rw [(natBytes_eq_nil n).2 hn]; simp
  · have hge := natValue_ge (minimal_natBytes n) (fun e => hn ((natBytes_eq_nil n).1 e))
    rw [natValue_natBytes] at hge
    false_or_by_contra
    have : 256 ^ k ≤ 256 ^ ((natBytes n).length - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ## Lengths -/

theorem decodeLength_encodeLength (n : Nat) (hn : n < maxLength) (rest : List UInt8) :
    decodeLength (encodeLength n ++ rest) = .ok (n, rest) := by
  unfold encodeLength
  by_cases h : n < 128
  · simp [h, decodeLength, Nat.mod_eq_of_lt (show n < 256 by omega)]
  · have hk := length_natBytes_lt (k := 126) hn
    have hne : natBytes n ≠ [] := fun e => by rw [natBytes_eq_nil] at e; omega
    have hk1 : 1 ≤ (natBytes n).length := List.length_pos_iff.2 hne
    have hb : ((0x80 + (natBytes n).length).toUInt8).toNat = 128 + (natBytes n).length := by
      rw [toNat_toUInt8]; omega
    have hm := minimal_natBytes n
    simp only [h, ↓reduceIte, List.cons_append, decodeLength, hb, Nat.add_sub_cancel_left,
      List.length_append, List.take_left', List.drop_left', natValue_natBytes]
    have hm' : ¬ (natBytes n).head? = some 0 := hm
    simp [show ¬ (128 + (natBytes n).length < 128) by omega, show (natBytes n).length ≠ 0 by omega,
      show (natBytes n).length ≠ 127 by omega, hm']

theorem decodeLength_sound {xs rest : List UInt8} {n : Nat}
    (h : decodeLength xs = .ok (n, rest)) : n < maxLength ∧ xs = encodeLength n ++ rest := by
  match xs with
  | [] => simp [decodeLength] at h
  | b :: tl =>
    have hb := b.toNat_lt
    simp only [decodeLength] at h
    split at h
    · next hlt =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by
        unfold maxLength
        have := Nat.le_self_pow (show 126 ≠ 0 by omega) 256
        omega, ?_⟩
      simp [encodeLength, hlt]
    · next hge =>
      split at h
      · cases h
      · next hk =>
        split at h
        · cases h
        · next hlen =>
          split at h
          · cases h
          · next hmin =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hm : Minimal (tl.take (b.toNat - 128)) := fun e => hmin (Or.inl e)
            have hv : 128 ≤ natValue (tl.take (b.toNat - 128)) := by
              have := hmin; omega
            have hl : (tl.take (b.toNat - 128)).length = b.toNat - 128 := by
              simp; omega
            refine ⟨?_, ?_⟩
            · have := natValue_lt (tl.take (b.toNat - 128))
              rw [hl] at this
              unfold maxLength
              have := Nat.pow_le_pow_right (show 0 < 256 by omega)
                (show b.toNat - 128 ≤ 126 by omega)
              omega
            · simp only [encodeLength, show ¬ (natValue (tl.take (b.toNat - 128)) < 128) by omega,
                ↓reduceIte, natBytes_natValue hm, hl, List.cons_append, List.take_append_drop,
                List.cons.injEq, and_true]
              apply UInt8.toNat_inj.1
              rw [toNat_toUInt8]; omega

/-! ## Identifiers -/

theorem ofByte_byte (t : Tag) (hv : t.Valid) : Tag.ofByte t.byte = some t := by
  obtain ⟨hc, hn⟩ := hv
  have hb : t.byte.toNat = t.cls * 64 + t.constructed.toNat * 32 + t.number := by
    unfold Tag.byte; rw [toNat_toUInt8]
    cases t.constructed <;> simp <;> omega
  unfold Tag.ofByte
  rw [hb]
  obtain ⟨c, k, n⟩ := t
  simp only at hc hn ⊢
  cases k <;> simp <;> omega

theorem ofByte_sound {b : UInt8} {t : Tag} (h : Tag.ofByte b = some t) : t.Valid ∧ t.byte = b := by
  unfold Tag.ofByte at h
  have hb := b.toNat_lt
  split at h
  · cases h
  · next hn =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨⟨by simp; omega, by simp; omega⟩, ?_⟩
    unfold Tag.byte
    apply UInt8.toNat_inj.1
    rw [toNat_toUInt8]
    simp only
    by_cases h2 : b.toNat / 32 % 2 = 1
    · simp [h2]; omega
    · have : b.toNat / 32 % 2 = 0 := by omega
      simp [this]; omega

/-! ## Items -/

theorem decode_encode (x : Tlv) (hv : x.Valid) (rest : List UInt8) :
    decode (encode x ++ rest) = .ok (x, rest) := by
  obtain ⟨ht, hl⟩ := hv
  simp only [encode, List.cons_append, decode, ofByte_byte _ ht, List.append_assoc,
    decodeLength_encodeLength _ hl, List.length_append,
    show ¬ (x.contents.length + rest.length < x.contents.length) by omega, ↓reduceIte,
    List.take_left', List.drop_left']

theorem decode_sound {xs rest : List UInt8} {x : Tlv} (h : decode xs = .ok (x, rest)) :
    x.Valid ∧ xs = encode x ++ rest := by
  match xs with
  | [] => simp [decode] at h
  | b :: tl =>
    simp only [decode] at h
    split at h
    · cases h
    · next t ht =>
      obtain ⟨htv, htb⟩ := ofByte_sound ht
      split at h
      · cases h
      · next n body hlen =>
        obtain ⟨hn, htl⟩ := decodeLength_sound hlen
        split at h
        · cases h
        · next hbody =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hl : (body.take n).length = n := by simp; omega
          refine ⟨⟨htv, by rw [hl]; exact hn⟩, ?_⟩
          simp only [encode, hl, htb, List.cons_append, List.append_assoc, List.take_append_drop,
            ← htl]

/-! ## Non-negative INTEGERs -/

theorem decodeNatContents_encodeNatContents (n : Nat) :
    decodeNatContents (encodeNatContents n) = some n := by
  unfold encodeNatContents
  have hm := minimal_natBytes n
  have hv := natValue_natBytes n
  match hb : natBytes n with
  | [] =>
    have : n = 0 := (natBytes_eq_nil n).1 hb
    subst this; rfl
  | [b] =>
    rw [hb] at hm hv
    have hb0 : b.toNat ≠ 0 := fun e => hm (by simp; exact UInt8.toNat_inj.1 (by simpa using e))
    have hvb : n = b.toNat := by simpa [natValue] using hv.symm
    by_cases h : b.toNat < 128
    · simp [h, decodeNatContents, hvb]
    · simp only [h, ↓reduceIte, decodeNatContents, show (0 : UInt8).toNat = 0 from rfl,
        show ¬ (128 ≤ 0) by omega, true_and]
      simp [natValue, hvb]
  | b :: c :: bs =>
    rw [hb] at hm hv
    have hb0 : b ≠ 0 := fun e => hm (by simp [e])
    by_cases h : b.toNat < 128
    · simp [h, decodeNatContents, hb0, show ¬ (128 ≤ b.toNat) by omega, hv]
    · simp only [h, ↓reduceIte, decodeNatContents, show (0 : UInt8).toNat = 0 from rfl,
        show ¬ (128 ≤ 0) by omega, true_and]
      have hv' : natValue (0 :: b :: c :: bs) = natValue (b :: c :: bs) := by
        simp [natValue]
      simp [hv', hv]

theorem decodeNatContents_sound {c : List UInt8} {n : Nat} (h : decodeNatContents c = some n) :
    encodeNatContents n = c := by
  match c with
  | [] => simp [decodeNatContents] at h
  | [b] =>
    simp only [decodeNatContents] at h
    split at h
    · next hb =>
      simp only [Option.some.injEq] at h
      subst h
      unfold encodeNatContents
      by_cases b0 : b.toNat = 0
      · have : b = 0 := UInt8.toNat_inj.1 (by simpa using b0)
        subst this
        simp only [show UInt8.toNat 0 = 0 from rfl]
        rw [(natBytes_eq_nil 0).2 rfl]
      · have hm : Minimal [b] := by
          simp [Minimal]; intro e; exact b0 (by simp [e])
        have := natBytes_natValue hm
        simp only [natValue, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add] at this
        rw [this]; simp [hb]
    · cases h
  | b :: c' :: rest =>
    simp only [decodeNatContents] at h
    split at h
    · cases h
    · next hb =>
      split at h
      · cases h
      · next hz =>
        simp only [Option.some.injEq] at h
        subst h
        unfold encodeNatContents
        by_cases b0 : b = 0
        · subst b0
          have hc : 128 ≤ c'.toNat := by simp at hz; omega
          have hm : Minimal (c' :: rest) := by
            simp [Minimal]; intro e; subst e; simp at hc
          have hv : natValue (0 :: c' :: rest) = natValue (c' :: rest) := by simp [natValue]
          rw [hv, natBytes_natValue hm]
          simp [show ¬ (c'.toNat < 128) by omega]
        · have hm : Minimal (b :: c' :: rest) := by simp [Minimal, b0]
          rw [natBytes_natValue hm]
          simp [show b.toNat < 128 by omega]

theorem length_encodeNatContents (n : Nat) :
    (encodeNatContents n).length ≤ (natBytes n).length + 1 := by
  unfold encodeNatContents
  split
  · simp
  · split <;> simp_all

end Silmaril.Proofs.Formats.Der
