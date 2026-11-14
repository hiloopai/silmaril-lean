module

public import Silmaril.Net.Qpack.Instruction.Defs
public import Silmaril.Net.Qpack.Table.Thms
public import Silmaril.Proofs.Net.Qpack.String

/-!
# QPACK encoder and decoder instructions: proofs

For `Silmaril.Net.Qpack.Instruction.Thms` (RFC 9204 §4.3, §4.4).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Qpack

open Silmaril.Net.Qpack
open Silmaril.Net.Hpack (Entry encodeInt decodeInt)

/-! ## Sequences -/

theorem decodeManyFuel_flatMap {α : Type} (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hrt : ∀ x rest, dec (enc x ++ rest) = some (x, rest)) (hne : ∀ x, enc x ≠ [])
    (xs : List α) (k : Nat) (hk : (xs.flatMap enc).length ≤ k) :
    decodeManyFuel dec k (xs.flatMap enc) = some xs := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    have hcat : (x :: xs).flatMap enc = enc x ++ xs.flatMap enc := by simp
    have hpos : 0 < (enc x).length := List.length_pos_iff.mpr (hne x)
    rw [hcat] at hk ⊢
    rw [List.length_append] at hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, tl, hbt⟩ : ∃ b tl, enc x ++ xs.flatMap enc = b :: tl := by
      cases h : enc x with
      | nil => exact absurd h (hne x)
      | cons b tl => exact ⟨b, tl ++ xs.flatMap enc, rfl⟩
    rw [hbt]
    simp only [decodeManyFuel]
    rw [← hbt, hrt]
    simp only [ih k (by omega)]

theorem decodeMany_flatMap {α : Type} (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hrt : ∀ x rest, dec (enc x ++ rest) = some (x, rest)) (hne : ∀ x, enc x ≠ [])
    (xs : List α) : decodeMany dec (xs.flatMap enc) = some xs :=
  decodeManyFuel_flatMap enc dec hrt hne xs _ (Nat.le_refl _)

/-! ## Encoder instructions -/

theorem decodeEncoderInstr_encode (i : EncoderInstr) (rest : List UInt8) :
    decodeEncoderInstr (i.encode ++ rest) = some (i, rest) := by
  cases i with
  | setCapacity c =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 5) (hi := 0x20) (by decide) (by decide) (by decide) c rest
    simp only [EncoderInstr.encode, he, decodeEncoderInstr, show ¬ 128 ≤ b.toNat by omega,
      show ¬ 64 ≤ b.toNat by omega, show 32 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]
  | duplicate i =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 5) (hi := 0x00) (by decide) (by decide) (by decide) i rest
    simp only [EncoderInstr.encode, he, decodeEncoderInstr, show ¬ 128 ≤ b.toNat by omega,
      show ¬ 64 ≤ b.toNat by omega, show ¬ 32 ≤ b.toNat by omega, ↓reduceIte, hd,
      Option.map_some]
  | insertLiteral n v =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ := encodeStringN_split (n := 6) (hi := 0x40) (by decide)
      (by decide) (by decide) (by decide) n (encodeStringN 8 0 v ++ rest)
    simp only [Nat.reduceSub, Nat.reducePow] at h2
    simp only [EncoderInstr.encode, List.append_assoc, he, decodeEncoderInstr,
      show ¬ 128 ≤ b.toNat by omega, show 64 ≤ b.toNat by omega, ↓reduceIte, hd]
    rw [decodeStringN_encodeStringN (n := 8) (hi := 0) (by decide) (by decide) (by decide)
      (by decide)]
  | insertNameRef s i v =>
    have hs : (if s then 0xc0 else 0x80) % 2 ^ 6 = 0 ∧ (if s then 0xc0 else 0x80) < 256 := by
      cases s <;> decide
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 6) (by decide) hs.1 hs.2 i (encodeStringN 8 0 v ++ rest)
    have hb : 128 ≤ b.toNat ∧ decide (192 ≤ b.toNat) = s := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
        decide_eq_false_iff_not] at h1 h2 ⊢ <;> omega
    simp only [EncoderInstr.encode, List.append_assoc, he, decodeEncoderInstr, hb.1, ↓reduceIte,
      hd]
    rw [decodeStringN_encodeStringN (n := 8) (hi := 0) (by decide) (by decide) (by decide)
      (by decide)]
    simp only [hb.2]

theorem EncoderInstr.encode_ne_nil (i : EncoderInstr) : i.encode ≠ [] := by
  cases i <;> simp [EncoderInstr.encode, encodeInt_ne_nil, encodeStringN_ne_nil]

theorem decodeEncoderInstrs_encode (is : List EncoderInstr) :
    decodeEncoderInstrs (encodeEncoderInstrs is) = some is :=
  decodeMany_flatMap _ _ decodeEncoderInstr_encode EncoderInstr.encode_ne_nil is

/-! ## Decoder instructions -/

theorem decodeDecoderInstr_encode (i : DecoderInstr) (rest : List UInt8) :
    decodeDecoderInstr (i.encode ++ rest) = some (i, rest) := by
  cases i with
  | sectionAck s =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 7) (hi := 0x80) (by decide) (by decide) (by decide) s rest
    simp only [DecoderInstr.encode, he, decodeDecoderInstr, show 128 ≤ b.toNat by omega,
      ↓reduceIte, hd, Option.map_some]
  | streamCancel s =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 6) (hi := 0x40) (by decide) (by decide) (by decide) s rest
    simp only [DecoderInstr.encode, he, decodeDecoderInstr, show ¬ 128 ≤ b.toNat by omega,
      show 64 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]
  | insertCountIncrement k =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 6) (hi := 0x00) (by decide) (by decide) (by decide) k rest
    simp only [DecoderInstr.encode, he, decodeDecoderInstr, show ¬ 128 ≤ b.toNat by omega,
      show ¬ 64 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]

theorem DecoderInstr.encode_ne_nil (i : DecoderInstr) : i.encode ≠ [] := by
  cases i <;> simp [DecoderInstr.encode, encodeInt_ne_nil]

theorem decodeDecoderInstrs_encode (is : List DecoderInstr) :
    decodeDecoderInstrs (encodeDecoderInstrs is) = some is :=
  decodeMany_flatMap _ _ decodeDecoderInstr_encode DecoderInstr.encode_ne_nil is

/-! ## Applying encoder instructions -/

namespace DynTable

/-- What an accepted instruction does to the table: an insertion or a capacity change. -/
theorem applyInstr_cases {t t' : DynTable} {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') :
    (∃ e, t.insert e = some t') ∨ (∃ c, t.setCapacity c = some t') := by
  have hins : ∀ e, t.insertOrErr e = .ok t' → ∃ e, t.insert e = some t' := by
    intro e he
    unfold DynTable.insertOrErr at he
    split at he
    · next h' => cases he; exact ⟨e, h'⟩
    · cases he
  cases i with
  | setCapacity c =>
    simp only [DynTable.applyInstr] at h
    split at h
    · next h' => cases h; exact .inr ⟨c, h'⟩
    · cases h
  | insertNameRef s i v =>
    cases s <;> simp only [DynTable.applyInstr] at h <;> split at h <;>
      first | exact .inl (hins _ h) | cases h
  | insertLiteral n v => exact .inl (hins _ h)
  | duplicate r =>
    simp only [DynTable.applyInstr] at h
    split at h
    · exact .inl (hins _ h)
    · cases h

theorem applyInstr_valid {t t' : DynTable} (ht : t.Valid) {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') : t'.Valid := by
  rcases applyInstr_cases h with ⟨e, he⟩ | ⟨c, hc⟩
  · exact DynTable.insert_valid ht he
  · exact DynTable.setCapacity_valid ht hc

theorem applyInstr_lookup {t t' : DynTable} {i : EncoderInstr} (h : t.applyInstr i = .ok t')
    {a : Nat} (ha : a < t.insertCount) {x : Entry} (hx : t'.lookupAbs a = some x) :
    t.lookupAbs a = some x := by
  rcases applyInstr_cases h with ⟨e, he⟩ | ⟨c, hc⟩
  · exact DynTable.insert_lookup_old he ha hx
  · exact DynTable.setCapacity_lookup hc hx

theorem applyInstr_insertCount {t t' : DynTable} {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') : t.insertCount ≤ t'.insertCount := by
  rcases applyInstr_cases h with ⟨e, he⟩ | ⟨c, hc⟩
  · rw [DynTable.insert_insertCount he]; omega
  · rw [DynTable.setCapacity_insertCount hc]; omega

theorem applyInstr_maxCapacity {t t' : DynTable} {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') : t'.maxCapacity = t.maxCapacity := by
  rcases applyInstr_cases h with ⟨e, he⟩ | ⟨c, hc⟩
  · exact DynTable.insert_maxCapacity he
  · exact DynTable.setCapacity_maxCapacity hc

theorem applyInstr_error {t : DynTable} {i : EncoderInstr} {err : QpackError}
    (h : t.applyInstr i = .error err) : err = .encoderStreamError := by
  have hins : ∀ e, t.insertOrErr e = .error err → err = .encoderStreamError := by
    intro e he
    unfold DynTable.insertOrErr at he
    split at he
    · cases he
    · cases he; rfl
  cases i with
  | setCapacity c =>
    simp only [DynTable.applyInstr] at h
    split at h
    · cases h
    · cases h; rfl
  | insertNameRef s i v =>
    cases s <;> simp only [DynTable.applyInstr] at h <;> split at h <;>
      first | exact hins _ h | (cases h; rfl)
  | insertLiteral n v => exact hins _ h
  | duplicate r =>
    simp only [DynTable.applyInstr] at h
    split at h
    · exact hins _ h
    · cases h; rfl

theorem applyInstrs_valid {t t' : DynTable} (ht : t.Valid) {is : List EncoderInstr}
    (h : t.applyInstrs is = .ok t') : t'.Valid := by
  induction is generalizing t with
  | nil => simp only [DynTable.applyInstrs, Except.ok.injEq] at h; exact h ▸ ht
  | cons i is ih =>
    simp only [DynTable.applyInstrs] at h
    split at h
    · next t₁ h₁ => exact ih (applyInstr_valid ht h₁) h
    · cases h

theorem applyInstrs_insertCount {t t' : DynTable} {is : List EncoderInstr}
    (h : t.applyInstrs is = .ok t') : t.insertCount ≤ t'.insertCount := by
  induction is generalizing t with
  | nil => simp only [DynTable.applyInstrs, Except.ok.injEq] at h; exact h ▸ Nat.le_refl _
  | cons i is ih =>
    simp only [DynTable.applyInstrs] at h
    split at h
    · next t₁ h₁ => exact Nat.le_trans (applyInstr_insertCount h₁) (ih h)
    · cases h

theorem applyInstrs_lookup {t t' : DynTable} {is : List EncoderInstr}
    (h : t.applyInstrs is = .ok t') {a : Nat} (ha : a < t.insertCount) {x : Entry}
    (hx : t'.lookupAbs a = some x) : t.lookupAbs a = some x := by
  induction is generalizing t with
  | nil => simp only [DynTable.applyInstrs, Except.ok.injEq] at h; exact h ▸ hx
  | cons i is ih =>
    simp only [DynTable.applyInstrs] at h
    split at h
    · next t₁ h₁ =>
      exact applyInstr_lookup h₁ ha
        (ih h (Nat.lt_of_lt_of_le ha (applyInstr_insertCount h₁)))
    · cases h

end DynTable

end Silmaril.Proofs.Net.Qpack
