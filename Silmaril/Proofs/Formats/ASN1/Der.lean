module

public import Silmaril.Formats.ASN1.Der.Defs
import Silmaril.Formats.ASN1.Digits.Thms
import Silmaril.Proofs.Formats.ASN1.Digits

/-! Proofs for `Silmaril.Formats.ASN1.Der.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.ASN1

open Silmaril Silmaril.Formats.ASN1

/-! ## Octet lemmas -/

theorem leadOctet_toNat (cls : TagClass) (c : Bool) {k : Nat} (hk : k < 32) :
    (leadOctet cls c k).toNat = cls.bits * 64 + (if c then 32 else 0) + k := by
  have := cls.bits_lt
  simp only [leadOctet, toNat_toUInt8]
  cases c <;> simp <;> omega

theorem leadOctet_div64 (cls : TagClass) (c : Bool) {k : Nat} (hk : k < 32) :
    (leadOctet cls c k).toNat / 64 = cls.bits := by
  rw [leadOctet_toNat cls c hk]; cases c <;> simp <;> omega

theorem leadOctet_mod32 (cls : TagClass) (c : Bool) {k : Nat} (hk : k < 32) :
    (leadOctet cls c k).toNat % 32 = k := by
  rw [leadOctet_toNat cls c hk]; cases c <;> simp <;> omega

theorem leadOctet_bit (cls : TagClass) (c : Bool) {k : Nat} (hk : k < 32) :
    decide ((leadOctet cls c k).toNat / 32 % 2 = 1) = c := by
  rw [leadOctet_toNat cls c hk]; cases c <;> simp <;> omega

theorem leadOctet_decomp (b : UInt8) :
    leadOctet (TagClass.ofBits (b.toNat / 64)) (decide (b.toNat / 32 % 2 = 1)) (b.toNat % 32) = b := by
  apply UInt8.toNat_inj.mp
  have hb := toNat_lt_256 b
  rw [leadOctet_toNat _ _ (Nat.mod_lt _ (by omega)), TagClass.bits_ofBits _ (by omega)]
  by_cases h : b.toNat / 32 % 2 = 1 <;> simp [h] <;> omega

theorem identifierOctets_iff (t : Tag) (c : Bool) (ids : List UInt8) :
    IdentifierOctets t c ids ↔ ids = encodeIdentifier t c := by
  constructor
  · intro h
    cases h with
    | low h => simp [encodeIdentifier, h]
    | high h hb =>
        rw [base128Octets_iff] at hb
        subst hb
        simp [encodeIdentifier, show ¬ t.number < 31 by omega]
  · rintro rfl
    unfold encodeIdentifier
    split
    · exact .low ‹_›
    · exact .high (by omega) ((base128Octets_iff _ _).mpr rfl)

theorem decodeIdentifier_eq_some {s r : List UInt8} {t : Tag} {c : Bool} :
    decodeIdentifier s = some (t, c, r) ↔ s = encodeIdentifier t c ++ r := by
  constructor
  · intro h
    cases s with
    | nil => simp [decodeIdentifier] at h
    | cons b r₀ =>
        simp only [decodeIdentifier] at h
        split_ifs at h with hk
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [encodeIdentifier, hk, ↓reduceIte, List.singleton_append]
          rw [leadOctet_decomp]
        · split at h
          · rename_i n r' hr
            split_ifs at h with hn
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            rw [readBase128_eq_some] at hr
            have h31 : b.toNat % 32 = 31 := by have := Nat.mod_lt b.toNat (show 32 > 0 by omega); omega
            simp only [encodeIdentifier, show ¬ n < 31 by omega, ↓reduceIte, List.cons_append, hr]
            congr 1
            rw [← h31, leadOctet_decomp]
          · cases h
  · rintro rfl
    unfold encodeIdentifier
    split
    · rename_i hn
      simp only [List.singleton_append, decodeIdentifier, leadOctet_div64 _ _ (by omega : t.number < 32),
        TagClass.ofBits_bits, leadOctet_mod32 _ _ (by omega : t.number < 32), hn, ↓reduceIte,
        leadOctet_bit _ _ (by omega : t.number < 32)]
    · rename_i hn
      have hr : readBase128 (base128 t.number ++ r) = some (t.number, r) := readBase128_eq_some.mpr rfl
      simp only [List.cons_append, decodeIdentifier, leadOctet_div64 _ _ (by omega : 31 < 32),
        TagClass.ofBits_bits, leadOctet_mod32 _ _ (by omega : 31 < 32), Nat.lt_irrefl, ↓reduceIte,
        leadOctet_bit _ _ (by omega : 31 < 32), hr, show 31 ≤ t.number by omega, ↓reduceIte]

theorem lengthOctets_iff (n : Nat) (lo : List UInt8) :
    LengthOctets n lo ↔ LengthOK n ∧ lo = encodeLength n := by
  constructor
  · intro h
    cases h with
    | short h => exact ⟨Or.inl h, by simp [encodeLength, h]⟩
    | long hne hlen h0 h128 =>
        rename_i bs
        refine ⟨Or.inr (by rw [beBytes_beNat h0]; exact hlen), ?_⟩
        simp [encodeLength, show ¬ beNat bs < 128 by omega, beBytes_beNat h0]
  · rintro ⟨hok, rfl⟩
    unfold encodeLength
    split
    · exact .short ‹_›
    · rename_i hn
      have hne : beBytes n ≠ [] := by rw [Ne, beBytes_eq_nil_iff]; omega
      have := LengthOctets.long hne (hok.resolve_left hn)
        (head?_beBytes_ne_zero n) (by rw [beNat_beBytes]; omega)
      rwa [beNat_beBytes] at this

theorem decodeLength_eq_some {s r : List UInt8} {n : Nat} :
    decodeLength s = some (n, r) ↔ LengthOK n ∧ s = encodeLength n ++ r := by
  constructor
  · intro h
    cases s with
    | nil => simp [decodeLength] at h
    | cons b r₀ =>
        simp only [decodeLength] at h
        split_ifs at h with hb hk h0
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Or.inl hb, by simp [encodeLength, hb]⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlen : (r₀.take (b.toNat - 128)).length = b.toNat - 128 := by
            simp only [List.length_take]; omega
          have hhead : (r₀.take (b.toNat - 128)).head? ≠ some 0 := fun h => h0 (Or.inl h)
          have hbb := beBytes_beNat hhead
          refine ⟨Or.inr (by rw [hbb]; omega), ?_⟩
          have hbyte : (128 + (b.toNat - 128)).toUInt8 = b := by
            apply UInt8.toNat_inj.mp
            simp only [toNat_toUInt8]
            have := toNat_lt_256 b
            omega
          simp only [encodeLength, show ¬ beNat (List.take (b.toNat - 128) r₀) < 128 by omega,
            ↓reduceIte, hbb, hlen, List.cons_append, List.take_append_drop, hbyte]
  · rintro ⟨hok, rfl⟩
    unfold encodeLength
    split
    · rename_i hn
      simp only [List.singleton_append, decodeLength, toNat_toUInt8,
        Nat.mod_eq_of_lt (show n < 256 by omega), hn, ↓reduceIte]
    · rename_i hn
      have hne : beBytes n ≠ [] := by rw [Ne, beBytes_eq_nil_iff]; omega
      have hpos := List.length_pos_iff.mpr hne
      have hk : (beBytes n).length ≤ 126 := hok.resolve_left hn
      have hb : ((128 + (beBytes n).length).toUInt8).toNat = 128 + (beBytes n).length := by
        simp only [toNat_toUInt8]; omega
      simp only [List.cons_append, decodeLength, hb, show ¬ 128 + (beBytes n).length < 128 by omega,
        ↓reduceIte, Nat.add_sub_cancel_left, List.take_left', List.drop_left', beNat_beBytes,
        head?_beBytes_ne_zero, List.length_append]
      simp [show ¬ (beBytes n).length = 0 by omega, show ¬ 126 < (beBytes n).length by omega,
        show ¬ n < 128 by omega]

theorem encodeIdentifier_ne_nil (t : Tag) (c : Bool) : encodeIdentifier t c ≠ [] := by
  unfold encodeIdentifier; split <;> simp

theorem encodeLength_ne_nil (n : Nat) : encodeLength n ≠ [] := by
  unfold encodeLength; split <;> simp

theorem two_le_length_encode (v : Value) : 2 ≤ (encode v).length := by
  cases v with
  | prim t b =>
      have := List.length_pos_iff.mpr (encodeIdentifier_ne_nil t false)
      have := List.length_pos_iff.mpr (encodeLength_ne_nil b.length)
      simp only [encode, List.length_append]; omega
  | cons t vs =>
      have := List.length_pos_iff.mpr (encodeIdentifier_ne_nil t true)
      have := List.length_pos_iff.mpr (encodeLength_ne_nil (encodeList vs).length)
      simp only [encode, List.length_append]; omega

/-! ## Relation versus encoder -/

theorem derList_of_wf : (vs : List Value) → Value.wfList vs = true → DerList (encodeList vs) vs
  | [], _ => .nil
  | .prim t b :: vs, h => by
      simp only [Value.wfList, Value.wf, Bool.and_eq_true, decide_eq_true_eq] at h
      have := DerList.prim ((identifierOctets_iff t false _).mpr rfl)
        ((lengthOctets_iff _ _).mpr ⟨h.1.2, rfl⟩) h.1.1 (derList_of_wf vs h.2)
      simpa [encode, encodeList, List.append_assoc] using this
  | .cons t kids :: vs, h => by
      simp only [Value.wfList, Value.wf, Bool.and_eq_true, decide_eq_true_eq] at h
      have := DerList.cons ((identifierOctets_iff t true _).mpr rfl)
        ((lengthOctets_iff _ _).mpr ⟨h.1.1.2, rfl⟩) h.1.1.1 (derList_of_wf kids h.1.2)
        (derList_of_wf vs h.2)
      simpa [encode, encodeList, List.append_assoc] using this
termination_by vs => sizeOf vs

theorem derList_iff (s : List UInt8) (vs : List Value) :
    DerList s vs ↔ Value.wfList vs = true ∧ s = encodeList vs := by
  constructor
  · intro h
    induction h with
    | nil => simp [Value.wfList, encodeList]
    | prim hid hlo ht _ ih =>
        rw [identifierOctets_iff] at hid
        rw [lengthOctets_iff] at hlo
        obtain ⟨hwf, rfl⟩ := ih
        subst hid; obtain ⟨hok, rfl⟩ := hlo
        simp [Value.wfList, Value.wf, encode, encodeList, ht, hok, hwf]
    | cons hid hlo ht _ _ ihc ih =>
        rw [identifierOctets_iff] at hid
        rw [lengthOctets_iff] at hlo
        obtain ⟨hwf, rfl⟩ := ih
        obtain ⟨hwfc, rfl⟩ := ihc
        subst hid; obtain ⟨hok, rfl⟩ := hlo
        simp [Value.wfList, Value.wf, encode, encodeList, ht, hok, hwf, hwfc]
  · rintro ⟨h, rfl⟩
    exact derList_of_wf vs h

theorem derRel_iff (s : List UInt8) (v : Value) : derRel s v ↔ v.wf = true ∧ encode v = s := by
  rw [derRel, derList_iff]
  simp only [Value.wfList, Bool.and_true, encodeList, List.append_nil]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

/-! ## Decoder correctness -/

theorem decode_complete_aux (fuel : Nat) :
    (∀ (v : Value) (r : List UInt8), v.wf = true → (encode v).length ≤ fuel →
      decodeTLV fuel (encode v ++ r) = some (v, r)) ∧
    (∀ vs : List Value, Value.wfList vs = true → (encodeList vs).length < fuel →
      decodeSeq fuel (encodeList vs) = some vs) := by
  induction fuel with
  | zero =>
      refine ⟨fun v r _ h => absurd h (by have := two_le_length_encode v; omega), fun vs _ h => ?_⟩
      omega
  | succ f ih =>
      refine ⟨fun v r hwf hlen => ?_, fun vs hwf hlen => ?_⟩
      · cases v with
        | prim t b =>
            simp only [Value.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
            have h₁ : decodeIdentifier (encodeIdentifier t false ++ (encodeLength b.length ++ (b ++ r))) =
                some (t, false, encodeLength b.length ++ (b ++ r)) := decodeIdentifier_eq_some.mpr rfl
            have h₂ : decodeLength (encodeLength b.length ++ (b ++ r)) = some (b.length, b ++ r) :=
              decodeLength_eq_some.mpr ⟨hwf.2, rfl⟩
            simp only [encode, List.append_assoc, decodeTLV, h₁, h₂]
            simp [hwf.1]
        | cons t kids =>
            simp only [Value.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
            have h₁ : decodeIdentifier (encodeIdentifier t true ++
                (encodeLength (encodeList kids).length ++ (encodeList kids ++ r))) =
                some (t, true, encodeLength (encodeList kids).length ++ (encodeList kids ++ r)) :=
              decodeIdentifier_eq_some.mpr rfl
            have h₂ : decodeLength (encodeLength (encodeList kids).length ++ (encodeList kids ++ r)) =
                some ((encodeList kids).length, encodeList kids ++ r) :=
              decodeLength_eq_some.mpr ⟨hwf.1.2, rfl⟩
            have hl₁ := List.length_pos_iff.mpr (encodeIdentifier_ne_nil t true)
            have hl₂ := List.length_pos_iff.mpr (encodeLength_ne_nil (encodeList kids).length)
            simp only [encode, List.length_append] at hlen
            have h₃ := ih.2 kids hwf.2 (by omega)
            simp only [encode, List.append_assoc, decodeTLV, h₁, h₂]
            simp [hwf.1.1, h₃]
      · cases vs with
        | nil => simp [encodeList, decodeSeq]
        | cons v vs =>
            simp only [Value.wfList, Bool.and_eq_true] at hwf
            simp only [encodeList, List.length_append] at hlen ⊢
            have h2 := two_le_length_encode v
            obtain ⟨x, xs, hx⟩ : ∃ x xs, encode v ++ encodeList vs = x :: xs :=
              List.exists_cons_of_ne_nil (by
                intro h; rw [List.append_eq_nil_iff] at h; rw [h.1] at h2; simp at h2)
            have h₁ := ih.1 v (encodeList vs) hwf.1 (by omega)
            have h₂ := ih.2 vs hwf.2 (by omega)
            rw [hx]
            simp only [decodeSeq]
            rw [← hx, h₁]
            simp [h₂]

theorem decode_sound_aux (fuel : Nat) :
    (∀ (s : List UInt8) (v : Value) (r : List UInt8), decodeTLV fuel s = some (v, r) →
      v.wf = true ∧ s = encode v ++ r) ∧
    (∀ (s : List UInt8) (vs : List Value), decodeSeq fuel s = some vs →
      Value.wfList vs = true ∧ s = encodeList vs) := by
  induction fuel with
  | zero =>
      refine ⟨fun s v r h => by simp [decodeTLV] at h, fun s vs h => ?_⟩
      cases s with
      | nil => simp only [decodeSeq, Option.some.injEq] at h; subst h; simp [Value.wfList, encodeList]
      | cons _ _ => simp [decodeSeq] at h
  | succ f ih =>
      refine ⟨fun s v r h => ?_, fun s vs h => ?_⟩
      · simp only [decodeTLV] at h
        split at h
        · cases h
        · rename_i t c s₁ hid
          rw [decodeIdentifier_eq_some] at hid
          split at h
          · cases h
          · rename_i n s₂ hlen
            rw [decodeLength_eq_some] at hlen
            split_ifs at h with hbad hc
            · split at h
              · rename_i vs hseq
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hwf, hs⟩ := ih.2 _ _ hseq
                have hn : (s₂.take n).length = n := by simp only [List.length_take]; omega
                rw [hs] at hn
                subst hc
                refine ⟨?_, ?_⟩
                · simp only [Value.wf, Bool.and_eq_true, decide_eq_true_eq, hwf, hn]
                  exact ⟨⟨fun h => hbad (Or.inr h), hlen.1⟩, trivial⟩
                · rw [hid, hlen.2, encode, hn, ← hs]
                  simp only [List.append_assoc, List.take_append_drop]
              · cases h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hn : (s₂.take n).length = n := by simp only [List.length_take]; omega
              simp only [Bool.not_eq_true] at hc
              subst hc
              refine ⟨?_, ?_⟩
              · simp only [Value.wf, Bool.and_eq_true, decide_eq_true_eq, hn]
                exact ⟨fun h => hbad (Or.inr h), hlen.1⟩
              · rw [hid, hlen.2, encode, hn]
                simp only [List.append_assoc, List.take_append_drop]
      · cases s with
        | nil => simp only [decodeSeq, Option.some.injEq] at h; subst h; simp [Value.wfList, encodeList]
        | cons x xs =>
            simp only [decodeSeq] at h
            split at h
            · cases h
            · rename_i v r htlv
              split at h
              · rename_i vs' hseq
                simp only [Option.some.injEq] at h
                subst h
                obtain ⟨hwf₁, hs₁⟩ := ih.1 _ _ _ htlv
                obtain ⟨hwf₂, hs₂⟩ := ih.2 _ _ hseq
                refine ⟨by simp [Value.wfList, hwf₁, hwf₂], ?_⟩
                rw [hs₁, hs₂, encodeList]
              · cases h

theorem decode_encode {v : Value} (h : v.wf = true) : decode (encode v) = some v := by
  have := (decode_complete_aux (encode v).length).1 v [] h (Nat.le_refl _)
  simp only [List.append_nil] at this
  simp [decode, this]

theorem decode_sound : derRel.DecoderSound decode := by
  intro s v h
  unfold decode at h
  split at h
  · rename_i v' hdec
    cases h
    obtain ⟨hwf, rfl⟩ := (decode_sound_aux s.length).1 _ _ _ hdec
    exact (derRel_iff _ _).mpr ⟨hwf, by simp⟩
  · cases h

theorem decode_complete : derRel.DecoderComplete decode := by
  intro s v h
  obtain ⟨hwf, rfl⟩ := (derRel_iff s v).mp h
  exact decode_encode hwf

end Silmaril.Proofs.Formats.ASN1
