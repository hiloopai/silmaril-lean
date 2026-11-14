module

public import Silmaril.Formats.ASN1.Universal.Defs
import Silmaril.Formats.ASN1.Digits.Thms
import Silmaril.Proofs.Formats.ASN1.Digits
import Silmaril.Formats.ASN1.Codec.Thms

/-! Proofs for `Silmaril.Formats.ASN1.Universal.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.ASN1

open Silmaril Silmaril.Formats.ASN1 Silmaril.Formats.ASN1.Content

/-! ## BOOLEAN, NULL, OCTET STRING -/

theorem lawful_boolean : Content.boolean.Lawful where
  dec_enc b _ := by cases b <;> decide
  enc_dec {bs b} h := by
    match bs, h with
    | [x], h =>
        simp only [Content.boolean] at h
        split_ifs at h with h₁ h₂ <;> cases h
        · exact ⟨trivial, by simp [Content.boolean, h₁]⟩
        · exact ⟨trivial, by simp [Content.boolean, h₂]⟩

theorem lawful_null : Content.null.Lawful where
  dec_enc _ _ := rfl
  enc_dec {bs u} h := by
    cases bs with
    | nil => exact ⟨trivial, rfl⟩
    | cons _ _ => cases h

theorem lawful_octets : Content.octets.Lawful where
  dec_enc _ _ := rfl
  enc_dec h := by cases h; exact ⟨trivial, rfl⟩

/-! ## INTEGER -/

theorem toNat_compl (b : UInt8) : (Content.compl b).toNat = 255 - b.toNat := by
  have := toNat_lt_256 b
  simp only [Content.compl, UInt8.toNat_sub_of_le _ _
    (show b ≤ 255 from UInt8.le_iff_toNat_le.mpr (by simp; omega))]
  simp

theorem compl_compl (b : UInt8) : Content.compl (Content.compl b) = b := by
  apply UInt8.toNat_inj.mp
  have := toNat_lt_256 b
  rw [toNat_compl, toNat_compl]; omega

theorem map_compl_compl (bs : List UInt8) : (bs.map compl).map compl = bs := by
  simp [List.map_map, Function.comp_def, compl_compl]

theorem beNat_zero_cons (bs : List UInt8) : beNat (0 :: bs) = beNat bs := by
  simp [beNat]

theorem natContent_head (n : Nat) : ∃ b bs, natContent n = b :: bs ∧ b.toNat < 128 := by
  unfold natContent
  split
  · exact ⟨0, [], rfl, by decide⟩
  · rename_i b bs _
    split_ifs with h
    · exact ⟨b, bs, rfl, h⟩
    · exact ⟨0, b :: bs, rfl, by decide⟩

theorem natOfContent?_natContent (n : Nat) : natOfContent? (natContent n) = some n := by
  unfold natContent
  split
  · rename_i h
    rw [beBytes_eq_nil_iff] at h
    subst h
    decide
  · rename_i b bs h
    have hb0 : b ≠ 0 := by
      intro hb; have := head?_beBytes_ne_zero n; rw [h, hb] at this; exact this rfl
    split_ifs with hb
    · have hb0' : (b == 0) = false := by simp [hb0]
      simp only [natOfContent?, hb, redundantZero, hb0', Bool.false_and, and_self, ↓reduceIte]
      rw [← h, beNat_beBytes]
    · have hb' : ¬ (b.toNat < 128) := hb
      simp only [natOfContent?, redundantZero, hb']
      rw [beNat_zero_cons, ← h, beNat_beBytes]
      simp

theorem natContent_of_natOfContent? {bs : List UInt8} {n : Nat} (h : natOfContent? bs = some n) :
    natContent n = bs := by
  match bs, h with
  | b :: r, h =>
      simp only [natOfContent?] at h
      split_ifs at h with hc
      cases h
      obtain ⟨hb, hz⟩ := hc
      by_cases hb0 : b = 0
      · subst hb0
        cases r with
        | nil =>
            have : beNat [0] = 0 := rfl
            rw [this]; unfold natContent; rw [(beBytes_eq_nil_iff 0).mpr rfl]
        | cons c cs =>
            simp only [redundantZero, beq_self_eq_true, decide_eq_false_iff_not, Bool.true_and,
              Nat.not_lt] at hz
            have hc0 : (c :: cs).head? ≠ some 0 := by
              simp only [List.head?_cons, ne_eq, Option.some.injEq]
              intro h; rw [h] at hz; simp at hz
            rw [beNat_zero_cons]
            unfold natContent
            rw [beBytes_beNat hc0]
            simp only [show ¬ c.toNat < 128 by omega, ↓reduceIte]
      · have hh : (b :: r).head? ≠ some 0 := by simp [hb0]
        unfold natContent
        rw [beBytes_beNat hh]
        simp [hb]

theorem intOfContent?_intContent (z : Int) : intOfContent? (intContent z) = some z := by
  unfold intContent
  split_ifs with hz
  · obtain ⟨b, bs, hbs, hb⟩ := natContent_head z.toNat
    rw [hbs]
    simp only [intOfContent?, hb, ↓reduceIte]
    rw [← hbs, natOfContent?_natContent]
    simp [Int.toNat_of_nonneg hz]
  · obtain ⟨b, bs, hbs, hb⟩ := natContent_head (-z - 1).toNat
    have hc : ¬ (compl b).toNat < 128 := by rw [toNat_compl]; omega
    have : intOfContent? ((natContent (-z - 1).toNat).map compl) =
        (natOfContent? (((natContent (-z - 1).toNat).map compl).map compl)).map
          (fun (n : Nat) => -(n : Int) - 1) := by
      rw [hbs]; simp only [List.map_cons, intOfContent?, hc, ↓reduceIte]
    rw [this, map_compl_compl, natOfContent?_natContent]
    simp only [Option.map_some, Option.some.injEq]
    omega

theorem intContent_of_intOfContent? {bs : List UInt8} {z : Int} (h : intOfContent? bs = some z) :
    intContent z = bs := by
  match bs, h with
  | b :: r, h =>
      simp only [intOfContent?] at h
      split_ifs at h with hb
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨n, hn, rfl⟩ := h
        simp [intContent, natContent_of_natOfContent? hn]
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨n, hn, rfl⟩ := h
        have h₁ : ¬ (0 ≤ -(n : Int) - 1) := by omega
        have h₂ : (-(-(n : Int) - 1) - 1).toNat = n := by omega
        simp only [intContent, h₁, ↓reduceIte]
        rw [h₂, natContent_of_natOfContent? hn, map_compl_compl]

theorem lawful_integer : Content.integer.Lawful where
  dec_enc z _ := intOfContent?_intContent z
  enc_dec h := ⟨trivial, intContent_of_intOfContent? h⟩

/-! ## BIT STRING -/

theorem lawful_bitString : Content.bitString.Lawful where
  dec_enc b h := by
    have : b.unused < 8 := by
      simp only [Content.bitString, BitString.ok, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    simp only [Content.bitString, UInt8.toNat_ofNat', Nat.toUInt8,
      Nat.mod_eq_of_lt (show b.unused < 256 by omega)]
    simp only [Content.bitString] at h
    simp [h]
  enc_dec {bs b} h := by
    match bs, h with
    | u :: r, h =>
        simp only [Content.bitString] at h
        split_ifs at h with hok
        cases h
        exact ⟨hok, by simp [Content.bitString]⟩

/-! ## OBJECT IDENTIFIER -/

theorem readArcs_flatMap (ns : List Nat) :
    ∀ fuel, (ns.flatMap base128).length ≤ fuel → readArcs fuel (ns.flatMap base128) = some ns := by
  induction ns with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons n ns ih =>
      intro fuel hf
      have hne := base128_ne_nil n
      have hpos := List.length_pos_iff.mpr hne
      simp only [List.flatMap_cons, List.length_append] at hf ⊢
      obtain ⟨x, xs, hx⟩ :=
        List.exists_cons_of_ne_nil (show base128 n ++ ns.flatMap base128 ≠ [] by simp [hne])
      cases fuel with
      | zero => omega
      | succ f =>
          rw [hx]
          simp only [readArcs]
          rw [← hx, readBase128_eq_some.mpr rfl]
          simp only [ih f (by omega), Option.map_some]

theorem readArcs_sound : ∀ (fuel : Nat) (s : List UInt8) (ns : List Nat),
    readArcs fuel s = some ns → s = ns.flatMap base128
  | fuel, [], ns, h => by
      cases fuel <;> (simp only [readArcs, Option.some.injEq] at h; subst h; rfl)
  | 0, _ :: _, _, h => by simp [readArcs] at h
  | fuel + 1, x :: xs, ns, h => by
      simp only [readArcs] at h
      split at h
      · rename_i n r hr
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨ns', hns', rfl⟩ := h
        rw [readBase128_eq_some.mp hr, readArcs_sound fuel r ns' hns']
        simp
      · cases h

theorem oidOfContent?_oidContent {arcs : List Nat} (h : oidWF arcs) :
    oidOfContent? (oidContent arcs) = some arcs := by
  match arcs, h with
  | a :: b :: rest, h =>
      simp only [oidWF] at h
      obtain ⟨ha, hb⟩ := h
      simp only [oidContent, oidOfContent?, readArcs_flatMap _ _ (Nat.le_refl _),
        Option.some.injEq]
      unfold splitFirst
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
      · have := hb (by omega); simp only [Nat.mul_zero, Nat.zero_add, this, ↓reduceIte]
      · have := hb (by omega)
        simp [show ¬ 40 * 1 + b < 40 by omega, show 40 * 1 + b < 80 by omega]
      · simp [show ¬ 40 * 2 + b < 40 by omega, show ¬ 40 * 2 + b < 80 by omega]

theorem oid_enc_dec {bs : List UInt8} {arcs : List Nat} (h : oidOfContent? bs = some arcs) :
    oidWF arcs ∧ oidContent arcs = bs := by
  unfold oidOfContent? at h
  split at h
  · rename_i x rest hr
    cases h
    have hs := readArcs_sound _ _ _ hr
    unfold splitFirst
    split_ifs with h₁ h₂
    · exact ⟨by simp [oidWF]; omega, by rw [hs, oidContent]; simp⟩
    · refine ⟨by simp [oidWF]; omega, ?_⟩
      rw [hs, oidContent]; congr 3; omega
    · refine ⟨by simp [oidWF], ?_⟩
      rw [hs, oidContent]; congr 3; omega
  · cases h

theorem lawful_oid : Content.oid.Lawful where
  dec_enc _ h := oidOfContent?_oidContent h
  enc_dec h := oid_enc_dec h

/-! ## UTF8String -/

theorem toByteArray_data_toList (b : ByteArray) : b.data.toList.toByteArray = b := by
  apply ByteArray.ext
  simp

theorem lawful_utf8 : Content.utf8.Lawful where
  dec_enc s _ := by
    simp only [Content.utf8, String.fromUTF8?, toByteArray_data_toList, s.isValidUTF8,
      ↓reduceDIte]
    rfl
  enc_dec {bs s} h := by
    simp only [Content.utf8, String.fromUTF8?] at h
    split at h
    · cases h
      exact ⟨trivial, List.toList_data_toByteArray⟩
    · cases h

/-! ## Derived codecs -/

theorem lawful_natural : natural.Lawful :=
  Codec.lawful_iso (Codec.lawful_refine (Codec.lawful_prim _ lawful_integer) _)
    (fun _ h => Int.toNat_of_nonneg h.2) (fun _ _ => rfl)

end Silmaril.Proofs.Formats.ASN1
